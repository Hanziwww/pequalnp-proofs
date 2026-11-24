import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_4073_17
    (hP10 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 10
      (fun (x : Fin 10 → Bool) =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) 18)
    (hP9 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9
      (fun (x : Fin 9 → Bool) =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
        x 5 && x 7 || x 6 && x 8 || x 8 && x 5) 15)
    (hDeg1 : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (u v : ℕ),
      PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 17 →
      (∀ g ∈ D.gates, (0 : ℕ) ∉ g.inputs) →
      (D.gates.filter (fun g => g.inputs.contains (10 : ℕ))).length = 1 →
      (∀ g ∈ D.gates, (10 : ℕ) ∈ g.inputs → g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) →
      let f := fun (x : Fin 10 → Bool) =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5;
      let w := fun (x : Fin 10 → Bool) (p : ℕ) => (D.wires (List.ofFn x ++ [!x 0])).getD p false;
      (∃ x, w x u = true ∧ w x v = false) → (∃ x, w x u = false ∧ w x v = true) →
      (∀ x, f x = true → w x u = true ∧ w x v = true) →
      ∃ x, f x = false ∧ w x u = true ∧ w x v = true)
    (hDeg2 : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (u v : ℕ),
      PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 17 →
      (D.gates.filter (fun g => g.inputs.contains (0 : ℕ) || g.inputs.contains (10 : ℕ))).length = 2 →
      (∃ g ∈ D.gates, (10 : ℕ) ∈ g.inputs) →
      (∀ g ∈ D.gates, ((0 : ℕ) ∈ g.inputs → g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        ((10 : ℕ) ∈ g.inputs → g.op = PEqualNP.CircuitLowerBounds.GateOp.and)) →
      let f := fun (x : Fin 10 → Bool) =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5;
      let w := fun (x : Fin 10 → Bool) (p : ℕ) => (D.wires (List.ofFn x ++ [!x 0])).getD p false;
      (∃ x, w x u = true ∧ w x v = false) → (∃ x, w x u = false ∧ w x v = true) →
      (∀ x, f x = true → w x u = true ∧ w x v = true) →
      ∃ x, f x = false ∧ w x u = true ∧ w x v = true) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (17 : ℕ) →       have x6 : (Fin (10 : ℕ) → Bool) → Bool := fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ));       have x7 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x7 : Fin (10 : ℕ) → Bool) (x8 : ℕ) => (x1.wires (List.ofFn x7 ++ [!x7 (0 : Fin (10 : ℕ))])).getD x8 Bool.false;       (∃ (x8 : Fin (10 : ℕ) → Bool), x7 x8 x2 = Bool.true ∧ x7 x8 x3 = Bool.false) → (∃ (x9 : Fin (10 : ℕ) → Bool), x7 x9 x2 = Bool.false ∧ x7 x9 x3 = Bool.true) → (∀ (x10 : Fin (10 : ℕ) → Bool), x6 x10 = Bool.true → x7 x10 x2 = Bool.true ∧ x7 x10 x3 = Bool.true) → ∃ (x11 : Fin (10 : ℕ) → Bool), x6 x11 = Bool.false ∧ x7 x11 x2 = Bool.true ∧ x7 x11 x3 = Bool.true := by
  intro C u v hfan hsize f10 wC huv1 huv2 hpos
  let P10 : (Fin 10 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  let P9 : (Fin 9 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
    x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let in11 (x : Fin 10 → Bool) : List Bool := List.ofFn x ++ [!x 0]
  let step (ws : List Bool) (g : Gate) : List Bool :=
    ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  let run (gs : List Gate) (ws : List Bool) : List Bool := gs.foldl step ws
  have eval_and (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have eval_or (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have eval_not (l : List Bool) : GateOp.not.eval l = !(l.headD false) := rfl
  have getD_snoc_end (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  have getD_snoc_ne (l : List Bool) (b : Bool) (i : ℕ) (hi : i ≠ l.length) :
      (l ++ [b]).getD i false = l.getD i false := by
    by_cases hlt : i < l.length
    · exact List.getD_append _ _ _ _ hlt
    · rw [List.getD_eq_default _ _ (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
          List.getD_eq_default _ _ (by omega)]
  have run_len (gs : List Gate) : ∀ ws : List Bool, (run gs ws).length = ws.length + gs.length := by
    induction gs with
    | nil => intro ws; simp only [run, List.foldl_nil, List.length_nil, Nat.add_zero]
    | cons g gs ih =>
      intro ws
      change (run gs (step ws g)).length = ws.length + (g :: gs).length
      rw [ih]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
  have run_keep (gs : List Gate) : ∀ (ws : List Bool) (i : ℕ), i < ws.length →
      (run gs ws).getD i false = ws.getD i false := by
    induction gs with
    | nil => intro ws i _; rfl
    | cons g gs ih =>
      intro ws i hi
      change (run gs (step ws g)).getD i false = ws.getD i false
      rw [ih (step ws g) i (by simp only [step, List.length_append, List.length_cons, List.length_nil]; omega)]
      exact List.getD_append _ _ _ _ hi
  have run_append (gs1 gs2 : List Gate) (ws : List Bool) :
      run (gs1 ++ gs2) ws = run gs2 (run gs1 ws) := List.foldl_append
  have in11_len (x : Fin 10 → Bool) : (in11 x).length = 11 := by
    simp only [in11, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
  have in11_lt (x : Fin 10 → Bool) (i : ℕ) (hi : i < 10) :
      (in11 x).getD i false = x ⟨i, hi⟩ := by
    have hlt : i < (List.ofFn x).length := by simpa only [List.length_ofFn] using hi
    rw [List.getD_append _ _ _ _ hlt, List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
  have in11_10 (x : Fin 10 → Bool) : (in11 x).getD 10 false = !x 0 := by
    simp only [in11, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (show (List.ofFn x).length ≤ 10 by simp),
      List.length_ofFn, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  have in11_0 (x : Fin 10 → Bool) : (in11 x).getD 0 false = x 0 := in11_lt x 0 (by omega)
  let evalSym (s : Bool ⊕ ℕ) (ws : List Bool) : Bool :=
    Sum.elim id (fun k => ws.getD k false) s
  let cleanGate (st : List (Bool ⊕ ℕ)) (outIdx : ℕ) (g : Gate) : (Bool ⊕ ℕ) × Option Gate :=
    let ins := g.inputs.map (fun i => st.getD i (Sum.inl false))
    GateOp.casesOn g.op
      (List.casesOn ins
        (Sum.inl true, none)
        (fun a rest => List.casesOn rest
          (a, none)
          (fun b _ => Sum.elim
            (fun ba => Bool.casesOn ba (Sum.inl false, none) (b, none))
            (fun ka => Sum.elim
              (fun bb => Bool.casesOn bb (Sum.inl false, none) (Sum.inr ka, none))
              (fun kb =>
                if ka == kb then (Sum.inr ka, none)
                else if (ka == 0 && kb == 10) || (ka == 10 && kb == 0) then (Sum.inl false, none)
                else (Sum.inr outIdx, some ⟨GateOp.and, [ka, kb]⟩)) b) a)))
      (List.casesOn ins
        (Sum.inl false, none)
        (fun a rest => List.casesOn rest
          (a, none)
          (fun b _ => Sum.elim
            (fun ba => Bool.casesOn ba (b, none) (Sum.inl true, none))
            (fun ka => Sum.elim
              (fun bb => Bool.casesOn bb (Sum.inr ka, none) (Sum.inl true, none))
              (fun kb =>
                if ka == kb then (Sum.inr ka, none)
                else if (ka == 0 && kb == 10) || (ka == 10 && kb == 0) then (Sum.inl true, none)
                else (Sum.inr outIdx, some ⟨GateOp.or, [ka, kb]⟩)) b) a)))
      (List.casesOn ins
        (Sum.inl true, none)
        (fun a _ => Sum.elim
          (fun ba => (Sum.inl (!ba), none))
          (fun ka =>
            if ka == 0 then (Sum.inr 10, none)
            else if ka == 10 then (Sum.inr 0, none)
            else (Sum.inr outIdx, some ⟨GateOp.not, [ka]⟩)) a))
      (fun _ => (Sum.inl false, none))
      (Sum.inl false, none)
  let cleanStep (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) : List (Bool ⊕ ℕ) × List Gate :=
    let r := cleanGate acc.1 (11 + acc.2.length) g
    (acc.1 ++ [r.1], Option.elim r.2 acc.2 (fun g' => acc.2 ++ [g']))
  let CleanProp (gs : List Gate) : Prop :=
    ∀ j < gs.length,
      let g := gs.getD j ⟨GateOp.or, []⟩
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2 ∧
      (∀ i ∈ g.inputs, i < 11 + j) ∧
      (g.op = GateOp.not → g.inputs.length = 1 ∧ (0 : ℕ) ∉ g.inputs ∧ (10 : ℕ) ∉ g.inputs) ∧
      ((g.op = GateOp.and ∨ g.op = GateOp.or) →
        g.inputs.length = 2 ∧ ¬ ((0 : ℕ) ∈ g.inputs ∧ (10 : ℕ) ∈ g.inputs))
  have cleanProp_fan (gs : List Gate) (hcl : CleanProp gs) :
      ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
    intro g hmem
    obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hmem
    have h := hcl j hj
    have hg : gs.getD j ⟨GateOp.or, []⟩ = g := by
      rw [List.getD_eq_getElem _ _ hj, hget]
    rw [hg] at h
    exact ⟨h.1, h.2.1⟩
  have cleanProp_snoc (gs : List Gate) (g : Gate) (hcl : CleanProp gs)
      (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2 ∧
        (∀ i ∈ g.inputs, i < 11 + gs.length) ∧
        (g.op = GateOp.not → g.inputs.length = 1 ∧ (0 : ℕ) ∉ g.inputs ∧ (10 : ℕ) ∉ g.inputs) ∧
        ((g.op = GateOp.and ∨ g.op = GateOp.or) →
          g.inputs.length = 2 ∧ ¬ ((0 : ℕ) ∈ g.inputs ∧ (10 : ℕ) ∈ g.inputs))) :
      CleanProp (gs ++ [g]) := by
    intro j hj
    simp only [List.length_append, List.length_cons, List.length_nil] at hj
    by_cases hlt : j < gs.length
    · have hget : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ :=
        List.getD_append _ _ _ _ hlt
      rw [hget]
      exact hcl j hlt
    · have hjeq : j = gs.length := by omega
      subst hjeq
      have hget : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hget]
      exact hg
  have clean_fold (gs_in : List Gate) :
      ∀ (st : List (Bool ⊕ ℕ)) (gs_out : List Gate) (gs_done : List Gate),
        (∀ g ∈ gs_in, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
        st.length = 11 + gs_done.length →
        gs_out.length ≤ gs_done.length →
        (∀ s ∈ st, Sum.elim (fun _ => True) (fun k => k < 11 + gs_out.length) s) →
        CleanProp gs_out →
        (∀ (x : Fin 10 → Bool) (i : ℕ), i < st.length →
          evalSym (st.getD i (Sum.inl false)) (run gs_out (in11 x)) =
            (run gs_done (in11 x)).getD i false) →
        let res := gs_in.foldl cleanStep (st, gs_out)
        res.1.length = 11 + (gs_done ++ gs_in).length ∧
        res.2.length ≤ (gs_done ++ gs_in).length ∧
        (∀ s ∈ res.1, Sum.elim (fun _ => True) (fun k => k < 11 + res.2.length) s) ∧
        CleanProp res.2 ∧
        (∀ (x : Fin 10 → Bool) (i : ℕ), i < res.1.length →
          evalSym (res.1.getD i (Sum.inl false)) (run res.2 (in11 x)) =
            (run (gs_done ++ gs_in) (in11 x)).getD i false) := by
    induction gs_in with
    | nil =>
      intro st gs_out gs_done _ hst hle hbd hcl hag
      simp only [List.foldl_nil, List.append_nil]
      exact ⟨hst, hle, hbd, hcl, hag⟩
    | cons g rest ih =>
      intro st gs_out gs_done hfin hst hle hbd hcl hag
      have hgfan := hfin g List.mem_cons_self
      have hrest_fin : ∀ g' ∈ rest, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
        fun g' hm => hfin g' (List.mem_cons_of_mem _ hm)
      have hget_bd (i : ℕ) : Sum.elim (fun _ => True) (fun k => k < 11 + gs_out.length) (st.getD i (Sum.inl false)) := by
        by_cases hi : i < st.length
        · rw [List.getD_eq_getElem _ _ hi]
          exact hbd _ (List.getElem_mem hi)
        · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
          trivial
      have hval (x : Fin 10 → Bool) (i : ℕ) :
          evalSym (st.getD i (Sum.inl false)) (run gs_out (in11 x)) =
            (run gs_done (in11 x)).getD i false := by
        by_cases hi : i < st.length
        · exact hag x i hi
        · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi),
              List.getD_eq_default _ _ (by rw [run_len, in11_len]; omega)]
          rfl
      have h010 (x : Fin 10 → Bool) :
          (run gs_out (in11 x)).getD 0 false = x 0 ∧
          (run gs_out (in11 x)).getD 10 false = !x 0 := by
        refine ⟨?_, ?_⟩
        · rw [run_keep gs_out (in11 x) 0 (by rw [in11_len]; omega), in11_0]
        · rw [run_keep gs_out (in11 x) 10 (by rw [in11_len]; omega), in11_10]
      let r := cleanGate st (11 + gs_out.length) g
      let st1 := st ++ [r.1]
      let gs1 := Option.elim r.2 gs_out (fun g' => gs_out ++ [g'])
      have hstep_ok :
          gs1.length ≤ gs_out.length + 1 ∧
          Sum.elim (fun _ => True) (fun k => k < 11 + gs1.length) r.1 ∧
          CleanProp gs1 ∧
          (∀ x : Fin 10 → Bool,
            evalSym r.1 (run gs1 (in11 x)) =
              g.op.eval (g.inputs.map fun i => (run gs_done (in11 x)).getD i false)) := by
        rcases hgfan.1 with hop | hop | hop
        · change g.op = GateOp.and at hop
          cases hgi : g.inputs with
          | nil =>
            simp only [r, gs1, cleanGate, hop, hgi, List.map_nil, Option.elim_none,
              eval_and, List.all_nil, evalSym, Sum.elim_inl]
            exact ⟨by omega, trivial, hcl, fun _ => rfl⟩
          | cons i1 t1 =>
            cases t1 with
            | nil =>
              simp only [r, gs1, cleanGate, hop, hgi, List.map_cons, List.map_nil,
                Option.elim_none, eval_and, List.all_cons, List.all_nil, id, Bool.and_true]
              exact ⟨by omega, hget_bd i1, hcl, fun x => hval x i1⟩
            | cons i2 t2 =>
              cases t2 with
              | nil =>
                have hb1 := hget_bd i1
                have hb2 := hget_bd i2
                dsimp only [r, gs1, cleanGate]
                rw [hop, hgi]
                simp only [List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id, Bool.and_true]
                cases hs1 : st.getD i1 (Sum.inl false) with
                | inl b1 =>
                  cases b1
                  · simp only [Sum.elim_inl, Option.elim_none, evalSym, id]
                    refine ⟨by omega, trivial, hcl, fun x => ?_⟩
                    have hv1 := hval x i1; rw [hs1] at hv1
                    simp only [evalSym, Sum.elim_inl, id] at hv1
                    rw [← hv1, Bool.false_and]
                  · simp only [Sum.elim_inl, Option.elim_none]
                    refine ⟨by omega, hb2, hcl, fun x => ?_⟩
                    have hv1 := hval x i1; rw [hs1] at hv1
                    simp only [evalSym, Sum.elim_inl, id] at hv1
                    rw [← hv1, Bool.true_and, hval x i2]
                | inr ka =>
                  rw [hs1] at hb1
                  simp only [Sum.elim_inr] at hb1
                  cases hs2 : st.getD i2 (Sum.inl false) with
                  | inl b2 =>
                    cases b2
                    · simp only [Sum.elim_inr, Sum.elim_inl, Option.elim_none, evalSym, id]
                      refine ⟨by omega, trivial, hcl, fun x => ?_⟩
                      have hv2 := hval x i2; rw [hs2] at hv2
                      simp only [evalSym, Sum.elim_inl, id] at hv2
                      rw [← hv2, Bool.and_false]
                    · simp only [Sum.elim_inr, Sum.elim_inl, Option.elim_none]
                      refine ⟨by omega, hb1, hcl, fun x => ?_⟩
                      have hv2 := hval x i2; rw [hs2] at hv2
                      simp only [evalSym, Sum.elim_inl, id] at hv2
                      have hv1 := hval x i1; rw [hs1] at hv1
                      rw [← hv2, Bool.and_true, ← hv1]
                  | inr kb =>
                    rw [hs2] at hb2
                    simp only [Sum.elim_inr] at hb2
                    simp only [Sum.elim_inr]
                    by_cases hkeq : ka = kb
                    · have hbeq : (ka == kb) = true := beq_iff_eq.mpr hkeq
                      simp only [hbeq, ↓reduceIte, Option.elim_none]
                      refine ⟨by omega, hb1, hcl, fun x => ?_⟩
                      have hv1 := hval x i1; rw [hs1] at hv1
                      have hv2 := hval x i2; rw [hs2] at hv2
                      rw [← hv1, ← hv2, hkeq, Bool.and_self]
                    · have hbeq : (ka == kb) = false := beq_eq_false_iff_ne.mpr hkeq
                      simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
                      by_cases hcomp : (ka == 0 && kb == 10) || (ka == 10 && kb == 0)
                      · simp only [hcomp, ↓reduceIte, Option.elim_none, evalSym, Sum.elim_inl, id]
                        refine ⟨by omega, trivial, hcl, fun x => ?_⟩
                        have hv1 := hval x i1; rw [hs1] at hv1
                        have hv2 := hval x i2; rw [hs2] at hv2
                        simp only [evalSym, Sum.elim_inr] at hv1 hv2
                        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcomp
                        rcases hcomp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                        · rw [← hv1, ← hv2, (h010 x).1, (h010 x).2]; cases x 0 <;> rfl
                        · rw [← hv1, ← hv2, (h010 x).1, (h010 x).2]; cases x 0 <;> rfl
                      · have hcompf : ((ka == 0 && kb == 10) || (ka == 10 && kb == 0)) = false :=
                          Bool.eq_false_iff.mpr hcomp
                        simp only [hcompf, Bool.false_eq_true, ↓reduceIte, Option.elim_some]
                        refine ⟨by simp only [List.length_append, List.length_cons, List.length_nil]; omega,
                          by simp only [Sum.elim_inr, List.length_append, List.length_cons, List.length_nil]; omega,
                          cleanProp_snoc gs_out ⟨GateOp.and, [ka, kb]⟩ hcl ?_, fun x => ?_⟩
                        · refine ⟨Or.inl rfl, by simp, ?_, fun h => (by cases h), fun _ => ⟨rfl, ?_⟩⟩
                          · intro z hz
                            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
                            rcases hz with rfl | rfl <;> assumption
                          · rintro ⟨h0m, h10m⟩
                            simp only [List.mem_cons, List.not_mem_nil, or_false] at h0m h10m
                            apply hcomp
                            simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
                            rcases h0m with rfl | rfl <;> rcases h10m with h10' | h10' <;> omega
                        · rw [run_append]
                          have hl : 11 + gs_out.length = (run gs_out (in11 x)).length := by
                            rw [run_len, in11_len]
                          simp only [evalSym, Sum.elim_inr, run, List.foldl_cons, List.foldl_nil, step,
                            hl, getD_snoc_end, List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id, Bool.and_true]
                          have hv1 := hval x i1; rw [hs1] at hv1
                          have hv2 := hval x i2; rw [hs2] at hv2
                          simp only [evalSym, Sum.elim_inr] at hv1 hv2
                          rw [hv1, hv2]
              | cons _ _ => have := hgfan.2; rw [hgi] at this; simp at this
        · change g.op = GateOp.or at hop
          cases hgi : g.inputs with
          | nil =>
            simp only [r, gs1, cleanGate, hop, hgi, List.map_nil, Option.elim_none,
              eval_or, List.any_nil, evalSym, Sum.elim_inl]
            exact ⟨by omega, trivial, hcl, fun _ => rfl⟩
          | cons i1 t1 =>
            cases t1 with
            | nil =>
              simp only [r, gs1, cleanGate, hop, hgi, List.map_cons, List.map_nil,
                Option.elim_none, eval_or, List.any_cons, List.any_nil, id, Bool.or_false]
              exact ⟨by omega, hget_bd i1, hcl, fun x => hval x i1⟩
            | cons i2 t2 =>
              cases t2 with
              | nil =>
                have hb1 := hget_bd i1
                have hb2 := hget_bd i2
                dsimp only [r, gs1, cleanGate]
                rw [hop, hgi]
                simp only [List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id, Bool.or_false]
                cases hs1 : st.getD i1 (Sum.inl false) with
                | inl b1 =>
                  cases b1
                  · simp only [Sum.elim_inl, Option.elim_none]
                    refine ⟨by omega, hb2, hcl, fun x => ?_⟩
                    have hv1 := hval x i1; rw [hs1] at hv1
                    simp only [evalSym, Sum.elim_inl, id] at hv1
                    rw [← hv1, Bool.false_or, hval x i2]
                  · simp only [Sum.elim_inl, Option.elim_none, evalSym, id]
                    refine ⟨by omega, trivial, hcl, fun x => ?_⟩
                    have hv1 := hval x i1; rw [hs1] at hv1
                    simp only [evalSym, Sum.elim_inl, id] at hv1
                    rw [← hv1, Bool.true_or]
                | inr ka =>
                  rw [hs1] at hb1
                  simp only [Sum.elim_inr] at hb1
                  cases hs2 : st.getD i2 (Sum.inl false) with
                  | inl b2 =>
                    cases b2
                    · simp only [Sum.elim_inr, Sum.elim_inl, Option.elim_none]
                      refine ⟨by omega, hb1, hcl, fun x => ?_⟩
                      have hv2 := hval x i2; rw [hs2] at hv2
                      simp only [evalSym, Sum.elim_inl, id] at hv2
                      have hv1 := hval x i1; rw [hs1] at hv1
                      rw [← hv2, Bool.or_false, ← hv1]
                    · simp only [Sum.elim_inr, Sum.elim_inl, Option.elim_none, evalSym, id]
                      refine ⟨by omega, trivial, hcl, fun x => ?_⟩
                      have hv2 := hval x i2; rw [hs2] at hv2
                      simp only [evalSym, Sum.elim_inl, id] at hv2
                      rw [← hv2, Bool.or_true]
                  | inr kb =>
                    rw [hs2] at hb2
                    simp only [Sum.elim_inr] at hb2
                    simp only [Sum.elim_inr]
                    by_cases hkeq : ka = kb
                    · have hbeq : (ka == kb) = true := beq_iff_eq.mpr hkeq
                      simp only [hbeq, ↓reduceIte, Option.elim_none]
                      refine ⟨by omega, hb1, hcl, fun x => ?_⟩
                      have hv1 := hval x i1; rw [hs1] at hv1
                      have hv2 := hval x i2; rw [hs2] at hv2
                      rw [← hv1, ← hv2, hkeq, Bool.or_self]
                    · have hbeq : (ka == kb) = false := beq_eq_false_iff_ne.mpr hkeq
                      simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
                      by_cases hcomp : (ka == 0 && kb == 10) || (ka == 10 && kb == 0)
                      · simp only [hcomp, ↓reduceIte, Option.elim_none, evalSym, Sum.elim_inl, id]
                        refine ⟨by omega, trivial, hcl, fun x => ?_⟩
                        have hv1 := hval x i1; rw [hs1] at hv1
                        have hv2 := hval x i2; rw [hs2] at hv2
                        simp only [evalSym, Sum.elim_inr] at hv1 hv2
                        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcomp
                        rcases hcomp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                        · rw [← hv1, ← hv2, (h010 x).1, (h010 x).2]; cases x 0 <;> rfl
                        · rw [← hv1, ← hv2, (h010 x).1, (h010 x).2]; cases x 0 <;> rfl
                      · have hcompf : ((ka == 0 && kb == 10) || (ka == 10 && kb == 0)) = false :=
                          Bool.eq_false_iff.mpr hcomp
                        simp only [hcompf, Bool.false_eq_true, ↓reduceIte, Option.elim_some]
                        refine ⟨by simp only [List.length_append, List.length_cons, List.length_nil]; omega,
                          by simp only [Sum.elim_inr, List.length_append, List.length_cons, List.length_nil]; omega,
                          cleanProp_snoc gs_out ⟨GateOp.or, [ka, kb]⟩ hcl ?_, fun x => ?_⟩
                        · refine ⟨Or.inr (Or.inl rfl), by simp, ?_, fun h => (by cases h), fun _ => ⟨rfl, ?_⟩⟩
                          · intro z hz
                            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
                            rcases hz with rfl | rfl <;> assumption
                          · rintro ⟨h0m, h10m⟩
                            simp only [List.mem_cons, List.not_mem_nil, or_false] at h0m h10m
                            apply hcomp
                            simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
                            rcases h0m with rfl | rfl <;> rcases h10m with h10' | h10' <;> omega
                        · rw [run_append]
                          have hl : 11 + gs_out.length = (run gs_out (in11 x)).length := by
                            rw [run_len, in11_len]
                          simp only [evalSym, Sum.elim_inr, run, List.foldl_cons, List.foldl_nil, step,
                            hl, getD_snoc_end, List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id, Bool.or_false]
                          have hv1 := hval x i1; rw [hs1] at hv1
                          have hv2 := hval x i2; rw [hs2] at hv2
                          simp only [evalSym, Sum.elim_inr] at hv1 hv2
                          rw [hv1, hv2]
              | cons _ _ => have := hgfan.2; rw [hgi] at this; simp at this
        · change g.op = GateOp.not at hop
          cases hgi : g.inputs with
          | nil =>
            simp only [r, gs1, cleanGate, hop, hgi, List.map_nil, Option.elim_none,
              eval_not, List.headD_nil, evalSym, Sum.elim_inl]
            exact ⟨by omega, trivial, hcl, fun _ => rfl⟩
          | cons i1 t1 =>
            have hb1 := hget_bd i1
            dsimp only [r, gs1, cleanGate]
            rw [hop, hgi]
            simp only [List.map_cons, eval_not, List.headD_cons]
            cases hs1 : st.getD i1 (Sum.inl false) with
            | inl b1 =>
              simp only [Sum.elim_inl, Option.elim_none, evalSym, id]
              refine ⟨by omega, trivial, hcl, fun x => ?_⟩
              have hv1 := hval x i1; rw [hs1] at hv1
              simp only [evalSym, Sum.elim_inl, id] at hv1
              rw [hv1]
            | inr ka =>
              rw [hs1] at hb1
              simp only [Sum.elim_inr] at hb1
              simp only [Sum.elim_inr]
              by_cases h0 : ka = 0
              · have hbeq : (ka == 0) = true := beq_iff_eq.mpr h0
                simp only [hbeq, ↓reduceIte, Option.elim_none]
                refine ⟨by omega, by simp only [Sum.elim_inr]; omega, hcl, fun x => ?_⟩
                have hv1 := hval x i1; rw [hs1, h0] at hv1
                simp only [evalSym, Sum.elim_inr, (h010 x).1, (h010 x).2] at hv1 ⊢
                rw [hv1]
              · have hbeq0 : (ka == 0) = false := beq_eq_false_iff_ne.mpr h0
                simp only [hbeq0, Bool.false_eq_true, ↓reduceIte]
                by_cases h10 : ka = 10
                · have hbeq10 : (ka == 10) = true := beq_iff_eq.mpr h10
                  simp only [hbeq10, ↓reduceIte, Option.elim_none]
                  refine ⟨by omega, by simp only [Sum.elim_inr]; omega, hcl, fun x => ?_⟩
                  have hv1 := hval x i1; rw [hs1, h10] at hv1
                  simp only [evalSym, Sum.elim_inr, (h010 x).1, (h010 x).2] at hv1 ⊢
                  rw [← hv1, Bool.not_not]
                · have hbeq10 : (ka == 10) = false := beq_eq_false_iff_ne.mpr h10
                  simp only [hbeq10, Bool.false_eq_true, ↓reduceIte, Option.elim_some]
                  refine ⟨by simp only [List.length_append, List.length_cons, List.length_nil]; omega,
                    by simp only [Sum.elim_inr, List.length_append, List.length_cons, List.length_nil]; omega,
                    cleanProp_snoc gs_out ⟨GateOp.not, [ka]⟩ hcl ?_, fun x => ?_⟩
                  · refine ⟨Or.inr (Or.inr rfl), by simp, ?_, fun _ => ?_, fun h => (by rcases h with h | h <;> cases h)⟩
                    · intro z hz
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
                      rw [hz]; exact hb1
                    · simp only [List.length_cons, List.length_nil, List.mem_cons, List.not_mem_nil, or_false]
                      exact ⟨trivial, fun h => h0 h.symm, fun h => h10 h.symm⟩
                  · rw [run_append]
                    have hl : 11 + gs_out.length = (run gs_out (in11 x)).length := by
                      rw [run_len, in11_len]
                    simp only [evalSym, Sum.elim_inr, run, List.foldl_cons, List.foldl_nil, step,
                      hl, getD_snoc_end, List.map_cons, List.map_nil, eval_not, List.headD_cons]
                    have hv1 := hval x i1; rw [hs1] at hv1
                    simp only [evalSym, Sum.elim_inr] at hv1
                    rw [hv1]
      have hgs1_ge : gs_out.length ≤ gs1.length := by
        dsimp only [gs1]
        cases r.2 with
        | none => exact Nat.le_refl _
        | some g' => simp only [Option.elim_some, List.length_append, List.length_cons, List.length_nil]; omega
      have hkeep_old (x : Fin 10 → Bool) (s : Bool ⊕ ℕ)
          (hs : Sum.elim (fun _ => True) (fun k => k < 11 + gs_out.length) s) :
          evalSym s (run gs1 (in11 x)) = evalSym s (run gs_out (in11 x)) := by
        cases s with
        | inl b => rfl
        | inr k =>
          simp only [Sum.elim_inr] at hs
          dsimp only [gs1]
          cases r.2 with
          | none => rfl
          | some g' =>
            simp only [Option.elim_some, evalSym, Sum.elim_inr, run_append]
            exact run_keep [g'] (run gs_out (in11 x)) k (by rw [run_len, in11_len]; exact hs)
      have hres := ih st1 gs1 (gs_done ++ [g]) hrest_fin
        (by simp only [st1, List.length_append, List.length_cons, List.length_nil]; omega)
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
        (by
          intro s hm
          simp only [st1, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
          rcases hm with hm | rfl
          · cases s with
            | inl _ => trivial
            | inr k =>
              have hk := hbd (Sum.inr k) hm
              simp only [Sum.elim_inr] at hk ⊢
              omega
          · exact hstep_ok.2.1)
        hstep_ok.2.2.1
        (by
          intro x i hi
          simp only [st1, List.length_append, List.length_cons, List.length_nil] at hi
          rw [run_append]
          change evalSym (st1.getD i (Sum.inl false)) (run gs1 (in11 x)) =
            (step (run gs_done (in11 x)) g).getD i false
          by_cases hlt : i < st.length
          · rw [List.getD_append _ _ _ _ hlt]
            have hne : i ≠ (run gs_done (in11 x)).length := by rw [run_len, in11_len]; omega
            rw [getD_snoc_ne _ _ _ hne]
            rw [hkeep_old x _ (hget_bd i)]
            exact hag x i hlt
          · have hieq : i = st.length := by omega
            subst hieq
            have hget : st1.getD st.length (Sum.inl false) = r.1 := by
              simp only [st1, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
                Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            have hlen : st.length = (run gs_done (in11 x)).length := by rw [run_len, in11_len, hst]
            rw [hget, hlen, getD_snoc_end]
            exact hstep_ok.2.2.2 x)
      simpa only [List.foldl_cons, cleanStep, List.append_assoc, List.singleton_append] using hres
  let st_init : List (Bool ⊕ ℕ) := (List.range 11).map Sum.inr
  have hclean := clean_fold C.gates st_init [] [] hfan
    (by simp only [st_init, List.length_map, List.length_range, List.length_nil, Nat.add_zero])
    (Nat.le_refl 0)
    (by
      intro s hm
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hm
      simp only [List.mem_range] at hk
      simp only [Sum.elim_inr, List.length_nil, Nat.add_zero]
      exact hk)
    (by intro j hj; simp at hj)
    (by
      intro x i hi
      have hget : st_init.getD i (Sum.inl false) = Sum.inr i := by
        rw [List.getD_eq_getElem _ _ hi]
        simp only [st_init, List.getElem_map, List.getElem_range]
      rw [hget]
      rfl)
  simp only [List.nil_append] at hclean
  let res1 := C.gates.foldl cleanStep (st_init, [])
  let gs1 := res1.2
  have hgs1_len : gs1.length ≤ 17 := by
    have h1 : gs1.length ≤ C.gates.length := hclean.2.1
    change C.gates.length ≤ 17 at hsize
    omega
  have hgs1_clean : CleanProp gs1 := hclean.2.2.2.1
  have hst1_val (x : Fin 10 → Bool) (i : ℕ) :
      evalSym (res1.1.getD i (Sum.inl false)) (run gs1 (in11 x)) = wC x i := by
    by_cases hi : i < res1.1.length
    · exact hclean.2.2.2.2 x i hi
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
      have hl : (C.wires (in11 x)).length = 11 + C.gates.length := by
        change (run C.gates (in11 x)).length = 11 + C.gates.length
        rw [run_len, in11_len]
      have hlen1 : res1.1.length = 11 + C.gates.length := hclean.1
      have hge : (C.wires (in11 x)).length ≤ i := by omega
      exact (List.getD_eq_default _ _ hge).symm
  have hu1_inr : ∃ u' < 11 + gs1.length, res1.1.getD u (Sum.inl false) = Sum.inr u' := by
    cases hsu : res1.1.getD u (Sum.inl false) with
    | inl b =>
      cases b
      · obtain ⟨x, hx1, _⟩ := huv1
        have h := hst1_val x u; rw [hsu] at h
        simp only [evalSym, Sum.elim_inl, id] at h
        rw [← h] at hx1; cases hx1
      · obtain ⟨x, hx1, _⟩ := huv2
        have h := hst1_val x u; rw [hsu] at h
        simp only [evalSym, Sum.elim_inl, id] at h
        rw [← h] at hx1; cases hx1
    | inr u' =>
      by_cases hu : u < res1.1.length
      · have hm : Sum.inr u' ∈ res1.1 := by
          rw [← hsu, List.getD_eq_getElem _ _ hu]
          exact List.getElem_mem hu
        exact ⟨u', hclean.2.2.1 _ hm, rfl⟩
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hu)] at hsu
        cases hsu
  have hv1_inr : ∃ v' < 11 + gs1.length, res1.1.getD v (Sum.inl false) = Sum.inr v' := by
    cases hsv : res1.1.getD v (Sum.inl false) with
    | inl b =>
      cases b
      · obtain ⟨x, _, hx2⟩ := huv2
        have h := hst1_val x v; rw [hsv] at h
        simp only [evalSym, Sum.elim_inl, id] at h
        rw [← h] at hx2; cases hx2
      · obtain ⟨x, _, hx2⟩ := huv1
        have h := hst1_val x v; rw [hsv] at h
        simp only [evalSym, Sum.elim_inl, id] at h
        rw [← h] at hx2; cases hx2
    | inr v' =>
      by_cases hv : v < res1.1.length
      · have hm : Sum.inr v' ∈ res1.1 := by
          rw [← hsv, List.getD_eq_getElem _ _ hv]
          exact List.getElem_mem hv
        exact ⟨v', hclean.2.2.1 _ hm, rfl⟩
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hv)] at hsv
        cases hsv
  obtain ⟨u1, hu1_lt, hu1_eq⟩ := hu1_inr
  obtain ⟨v1, hv1_lt, hv1_eq⟩ := hv1_inr
  have hu1_val (x : Fin 10 → Bool) : (run gs1 (in11 x)).getD u1 false = wC x u := by
    have h := hst1_val x u; rw [hu1_eq] at h; exact h
  have hv1_val (x : Fin 10 → Bool) : (run gs1 (in11 x)).getD v1 false = wC x v := by
    have h := hst1_val x v; rw [hv1_eq] at h; exact h
  let drop (t i : ℕ) : ℕ := if i < t then i else i - 1
  let dropGate (t : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (drop t)⟩
  have drop_sim (t : ℕ) (tail : List Gate) :
      ∀ (ws zs : List Bool),
        ws.length = zs.length + 1 → t ≤ zs.length →
        (∀ g ∈ tail, t ∉ g.inputs) →
        (∀ i, i ≠ t → ws.getD i false = zs.getD (drop t i) false) →
        ∀ i, i ≠ t → (run tail ws).getD i false = (run (tail.map (dropGate t)) zs).getD (drop t i) false := by
    induction tail with
    | nil => intro ws zs _ _ _ h i hi; exact h i hi
    | cons g rest ih =>
      intro ws zs hlen ht hno h i hi
      have hgno : t ∉ g.inputs := hno g List.mem_cons_self
      have hval : g.op.eval (g.inputs.map fun k => ws.getD k false) =
          (dropGate t g).op.eval ((dropGate t g).inputs.map fun k => zs.getD k false) := by
        simp only [dropGate, List.map_map]
        congr 1
        refine List.map_congr_left fun k hk => h k (fun heq => hgno (heq ▸ hk))
      change (run rest (step ws g)).getD i false =
        (run (rest.map (dropGate t)) (step zs (dropGate t g))).getD (drop t i) false
      apply ih (step ws g) (step zs (dropGate t g))
        (by simp only [step, List.length_append, List.length_cons, List.length_nil]; omega)
        (by simp only [step, List.length_append, List.length_cons, List.length_nil]; omega)
        (fun g' hm => hno g' (List.mem_cons_of_mem _ hm))
        (by
          intro j hj
          by_cases hjw : j = ws.length
          · have hdj : drop t j = zs.length := by dsimp only [drop]; split_ifs <;> omega
            rw [hdj, hjw]
            simp only [step, getD_snoc_end, hval]
          · have hdjne : drop t j ≠ zs.length := by dsimp only [drop]; split_ifs <;> omega
            simp only [step]
            rw [getD_snoc_ne _ _ _ hjw, getD_snoc_ne _ _ _ hdjne, h j hj])
        i hi
  have prune_exists : ∀ (n : ℕ) (gs : List Gate) (ua va : ℕ),
      gs.length = n → gs.length ≤ 17 → CleanProp gs →
      ua < 11 + gs.length → va < 11 + gs.length →
      (∀ x, (run gs (in11 x)).getD ua false = wC x u) →
      (∀ x, (run gs (in11 x)).getD va false = wC x v) →
      ∃ (gs2 : List Gate) (u2 v2 : ℕ),
        gs2.length ≤ 17 ∧ CleanProp gs2 ∧
        u2 < 11 + gs2.length ∧ v2 < 11 + gs2.length ∧
        (∀ x, (run gs2 (in11 x)).getD u2 false = wC x u) ∧
        (∀ x, (run gs2 (in11 x)).getD v2 false = wC x v) ∧
        (∀ j < gs2.length, 11 + j = u2 ∨ 11 + j = v2 ∨
          ∃ j' < gs2.length, 11 + j ∈ (gs2.getD j' ⟨GateOp.or, []⟩).inputs) := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro gs ua va hlen h17 hcl hua hva huval hvval
      by_cases hreach : ∀ j < gs.length, 11 + j = ua ∨ 11 + j = va ∨
          ∃ j' < gs.length, 11 + j ∈ (gs.getD j' ⟨GateOp.or, []⟩).inputs
      · exact ⟨gs, ua, va, h17, hcl, hua, hva, huval, hvval, hreach⟩
      · have hex : ∃ j < gs.length, 11 + j ≠ ua ∧ 11 + j ≠ va ∧
            ∀ j' < gs.length, 11 + j ∉ (gs.getD j' ⟨GateOp.or, []⟩).inputs := by
          by_contra hnone
          apply hreach
          intro j hj
          by_contra hbad
          apply hnone
          refine ⟨j, hj, fun h => hbad (Or.inl h), fun h => hbad (Or.inr (Or.inl h)),
            fun j' hj' hm => hbad (Or.inr (Or.inr ⟨j', hj', hm⟩))⟩
        obtain ⟨j, hj, hju, hjv, hjno⟩ := hex
        let t := 11 + j
        let pref := gs.take j
        let suff := gs.drop (j + 1)
        let gs' := pref ++ suff.map (dropGate t)
        have hpref_len : pref.length = j := List.length_take_of_le (Nat.le_of_lt hj)
        have hsuff_len : suff.length = gs.length - (j + 1) := List.length_drop
        have hgs'_len : gs'.length = gs.length - 1 := by
          simp only [gs', List.length_append, hpref_len, List.length_map, hsuff_len]
          omega
        have hsplit : gs = pref ++ [gs.getD j ⟨GateOp.or, []⟩] ++ suff := by
          have hget : gs.getD j ⟨GateOp.or, []⟩ = gs[j] := List.getD_eq_getElem _ _ hj
          rw [hget]
          simp only [pref, suff, List.append_assoc, List.singleton_append,
            List.cons_getElem_drop_succ, List.take_append_drop]
        have hsuff_no : ∀ g ∈ suff, t ∉ g.inputs := by
          intro g hm
          obtain ⟨k, hk, hkg⟩ := List.mem_iff_getElem.mp hm
          have hjk : j + 1 + k < gs.length := by rw [hsuff_len] at hk; omega
          have hget : gs.getD (j + 1 + k) ⟨GateOp.or, []⟩ = g := by
            rw [List.getD_eq_getElem _ _ hjk, ← hkg]
            exact (List.getElem_drop (i := j + 1) (j := k)).symm
          rw [← hget]
          exact hjno (j + 1 + k) hjk
        have hdrop_small (z : ℕ) (hz : z < 11) : drop t z = z := by
          dsimp only [drop, t]; split_ifs <;> omega
        have hgs'_clean : CleanProp gs' := by
          intro k hk
          by_cases hkj : k < j
          · have hget : gs'.getD k ⟨GateOp.or, []⟩ = gs.getD k ⟨GateOp.or, []⟩ := by
              rw [List.getD_append _ _ _ _ (by rw [hpref_len]; exact hkj),
                  List.getD_eq_getElem _ _ (by rw [hpref_len]; exact hkj),
                  List.getD_eq_getElem _ _ (by omega)]
              exact List.getElem_take
            rw [hget]
            exact hcl k (by omega)
          · have hk' : k + 1 < gs.length := by omega
            have hks : k - j < suff.length := by rw [hsuff_len]; omega
            have hget : gs'.getD k ⟨GateOp.or, []⟩ = dropGate t (gs.getD (k + 1) ⟨GateOp.or, []⟩) := by
              have h1 : gs'.getD k ⟨GateOp.or, []⟩ =
                  (suff.map (dropGate t)).getD (k - j) ⟨GateOp.or, []⟩ := by
                have hge : pref.length ≤ k := by rw [hpref_len]; omega
                simp only [gs', List.getD_eq_getElem?_getD, List.getElem?_append_right hge, hpref_len]
              rw [h1, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hks),
                  List.getElem_map, List.getD_eq_getElem _ _ hk']
              congr 1
              have hidx : j + 1 + (k - j) = k + 1 := by omega
              rw [List.getElem_drop]
              congr 1
            rw [hget]
            have ho := hcl (k + 1) hk'
            have hno_t := hjno (k + 1) hk'
            change t ∉ (gs.getD (k + 1) ⟨GateOp.or, []⟩).inputs at hno_t
            refine ⟨ho.1, by simpa only [dropGate, List.length_map] using ho.2.1, ?_, ?_, ?_⟩
            · intro i hi
              obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
              have hi0lt := ho.2.2.1 i0 hi0
              have hi0ne : i0 ≠ t := by intro h; apply hno_t; rw [← h]; exact hi0
              dsimp only [drop, t] at *; split_ifs <;> omega
            · intro hnot
              have h010 := ho.2.2.2.1 hnot
              refine ⟨by simpa only [dropGate, List.length_map] using h010.1, ?_, ?_⟩
              · intro hm0
                obtain ⟨i0, hi0, heq0⟩ := List.mem_map.mp hm0
                have hi0ne : i0 ≠ t := by intro h; apply hno_t; rw [← h]; exact hi0
                have hiz : i0 = 0 := by dsimp only [drop, t] at heq0; split_ifs at heq0 <;> omega
                apply h010.2.1; rw [← hiz]; exact hi0
              · intro hm10
                obtain ⟨i0, hi0, heq10⟩ := List.mem_map.mp hm10
                have hi0ne : i0 ≠ t := by intro h; apply hno_t; rw [← h]; exact hi0
                have hiz : i0 = 10 := by dsimp only [drop, t] at heq10; split_ifs at heq10 <;> omega
                apply h010.2.2; rw [← hiz]; exact hi0
            · intro hbin
              have hbo := ho.2.2.2.2 hbin
              refine ⟨by simpa only [dropGate, List.length_map] using hbo.1, ?_⟩
              rintro ⟨hm0, hm10⟩
              obtain ⟨i0, hi0, heq0⟩ := List.mem_map.mp hm0
              obtain ⟨i1, hi1, heq10⟩ := List.mem_map.mp hm10
              have hi0ne : i0 ≠ t := by intro h; apply hno_t; rw [← h]; exact hi0
              have hi1ne : i1 ≠ t := by intro h; apply hno_t; rw [← h]; exact hi1
              have hiz0 : i0 = 0 := by dsimp only [drop, t] at heq0; split_ifs at heq0 <;> omega
              have hiz10 : i1 = 10 := by dsimp only [drop, t] at heq10; split_ifs at heq10 <;> omega
              exact hbo.2 ⟨by rw [← hiz0]; exact hi0, by rw [← hiz10]; exact hi1⟩
        have hsim_all (x : Fin 10 → Bool) (i : ℕ) (hi : i ≠ t) :
            (run gs' (in11 x)).getD (drop t i) false = (run gs (in11 x)).getD i false := by
          symm
          conv_lhs => rw [hsplit]
          rw [run_append, run_append, run_append]
          let w0 := run pref (in11 x)
          have hw0 : w0.length = t := by dsimp only [w0, t]; rw [run_len, in11_len, hpref_len]
          let w1 := run [gs.getD j ⟨GateOp.or, []⟩] w0
          have hw1 : w1.length = w0.length + 1 := by
            dsimp only [w1]; rw [run_len]; simp only [List.length_cons, List.length_nil]
          apply drop_sim t suff w1 w0 hw1 (by omega) hsuff_no ?_ i hi
          intro z hz
          have hz_ne : z ≠ w0.length := by omega
          by_cases hlt : z < t
          · have hdz : drop t z = z := by dsimp only [drop]; split_ifs; rfl
            rw [hdz]
            exact getD_snoc_ne w0 _ z hz_ne
          · have hdz : drop t z = z - 1 := by dsimp only [drop]; split_ifs; omega
            rw [hdz, List.getD_eq_default w1 _ (by omega), List.getD_eq_default w0 _ (by omega)]
        exact ih gs'.length (by omega) gs' (drop t ua) (drop t va) rfl (by omega) hgs'_clean
          (by dsimp only [drop, t]; split_ifs <;> omega)
          (by dsimp only [drop, t]; split_ifs <;> omega)
          (fun x => (hsim_all x ua (fun h => hju h.symm)).trans (huval x))
          (fun x => (hsim_all x va (fun h => hjv h.symm)).trans (hvval x))
  obtain ⟨gs2, u2, v2, hgs2_len, hgs2_clean, hu2_lt, hv2_lt, hu2_val, hv2_val, hgs2_reach⟩ :=
    prune_exists gs1.length gs1 u1 v1 rfl hgs1_len hgs1_clean hu1_lt hv1_lt hu1_val hv1_val
  let D2 : Circuit := ⟨gs2, 0⟩
  have hD2_fan : FanInTwo D2 := cleanProp_fan gs2 hgs2_clean
  have hD2_size : D2.size ≤ 17 := hgs2_len
  have hw2_eq (x : Fin 10 → Bool) :
      (D2.wires (in11 x)).getD u2 false = wC x u ∧
      (D2.wires (in11 x)).getD v2 false = wC x v := ⟨hu2_val x, hv2_val x⟩
  have hD2_uv1 : ∃ x, (D2.wires (in11 x)).getD u2 false = true ∧ (D2.wires (in11 x)).getD v2 false = false := by
    obtain ⟨x, hx1, hx2⟩ := huv1
    exact ⟨x, (hw2_eq x).1.trans hx1, (hw2_eq x).2.trans hx2⟩
  have hD2_uv2 : ∃ x, (D2.wires (in11 x)).getD u2 false = false ∧ (D2.wires (in11 x)).getD v2 false = true := by
    obtain ⟨x, hx1, hx2⟩ := huv2
    exact ⟨x, (hw2_eq x).1.trans hx1, (hw2_eq x).2.trans hx2⟩
  have hD2_pos : ∀ x, P10 x = true →
      (D2.wires (in11 x)).getD u2 false = true ∧ (D2.wires (in11 x)).getD v2 false = true := by
    intro x hx
    have hp := hpos x hx
    exact ⟨(hw2_eq x).1.trans hp.1, (hw2_eq x).2.trans hp.2⟩
  have hu2_ne0 : u2 ≠ 0 := by
    intro h0
    let xA : Fin 10 → Bool := ![false, true, true, false, false, false, false, false, false, false]
    have hxA : P10 xA = true := by decide
    have h := (hD2_pos xA hxA).1
    rw [h0] at h
    have hkeep : (run gs2 (in11 xA)).getD 0 false = false := by
      rw [run_keep gs2 (in11 xA) 0 (by rw [in11_len]; omega), in11_0]
      rfl
    change (run gs2 (in11 xA)).getD 0 false = true at h
    rw [hkeep] at h; cases h
  have hv2_ne0 : v2 ≠ 0 := by
    intro h0
    let xA : Fin 10 → Bool := ![false, true, true, false, false, false, false, false, false, false]
    have hxA : P10 xA = true := by decide
    have h := (hD2_pos xA hxA).2
    rw [h0] at h
    have hkeep : (run gs2 (in11 xA)).getD 0 false = false := by
      rw [run_keep gs2 (in11 xA) 0 (by rw [in11_len]; omega), in11_0]
      rfl
    change (run gs2 (in11 xA)).getD 0 false = true at h
    rw [hkeep] at h; cases h
  have hu2_ne10 : u2 ≠ 10 := by
    intro h10
    let xB : Fin 10 → Bool := ![true, true, false, false, false, false, false, false, false, false]
    have hxB : P10 xB = true := by decide
    have h := (hD2_pos xB hxB).1
    rw [h10] at h
    have hkeep : (run gs2 (in11 xB)).getD 10 false = false := by
      rw [run_keep gs2 (in11 xB) 10 (by rw [in11_len]; omega), in11_10]
      rfl
    change (run gs2 (in11 xB)).getD 10 false = true at h
    rw [hkeep] at h; cases h
  have hv2_ne10 : v2 ≠ 10 := by
    intro h10
    let xB : Fin 10 → Bool := ![true, true, false, false, false, false, false, false, false, false]
    have hxB : P10 xB = true := by decide
    have h := (hD2_pos xB hxB).2
    rw [h10] at h
    have hkeep : (run gs2 (in11 xB)).getD 10 false = false := by
      rw [run_keep gs2 (in11 xB) 10 (by rw [in11_len]; omega), in11_10]
      rfl
    change (run gs2 (in11 xB)).getD 10 false = true at h
    rw [hkeep] at h; cases h
  by_contra hno_wit
  have hD2_exact (x : Fin 10 → Bool) :
      ((D2.wires (in11 x)).getD u2 false && (D2.wires (in11 x)).getD v2 false) = P10 x := by
    cases hfx : P10 x
    · cases hu : (D2.wires (in11 x)).getD u2 false
      · rfl
      · cases hv : (D2.wires (in11 x)).getD v2 false
        · rfl
        · exfalso
          apply hno_wit
          exact ⟨x, hfx, (hw2_eq x).1.symm.trans hu, (hw2_eq x).2.symm.trans hv⟩
    · have hp := hD2_pos x hfx
      rw [hp.1, hp.2]; rfl
  have hD2_no_wit : ¬ ∃ x, P10 x = false ∧
      (D2.wires (in11 x)).getD u2 false = true ∧ (D2.wires (in11 x)).getD v2 false = true := by
    rintro ⟨x, hfx, hu, hv⟩
    exact hno_wit ⟨x, hfx, (hw2_eq x).1.symm.trans hu, (hw2_eq x).2.symm.trans hv⟩
  let n10 := (gs2.filter (fun g => g.inputs.contains (10 : ℕ))).length
  let n010 := (gs2.filter (fun g => g.inputs.contains (0 : ℕ) || g.inputs.contains (10 : ℕ))).length
  by_cases hn10 : n10 = 0
  · have hno10 : ∀ g ∈ gs2, (10 : ℕ) ∉ g.inputs := by
      intro g hm h10m
      have hfil : g ∈ gs2.filter (fun g => g.inputs.contains (10 : ℕ)) :=
        List.mem_filter.mpr ⟨hm, List.contains_iff_mem.mpr h10m⟩
      have hpos_l : 0 < n10 := List.length_pos_iff.mpr (List.ne_nil_of_mem hfil)
      omega
    let E10 : Circuit := ⟨gs2.map (dropGate 10) ++ [⟨GateOp.and, [drop 10 u2, drop 10 v2]⟩], 10 + gs2.length⟩
    apply hP10
    refine ⟨E10, ?_, ?_, ?_⟩
    · intro g hm
      simp only [E10, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with ⟨g0, hg0, rfl⟩ | rfl
      · have hf := hD2_fan g0 hg0
        exact ⟨hf.1, by simpa only [dropGate, List.length_map] using hf.2⟩
      · exact ⟨Or.inl rfl, by simp⟩
    · change E10.gates.length ≤ 18
      dsimp only [E10]
      simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
      omega
    · intro x
      have hsim : ∀ i, i ≠ 10 →
          (run gs2 (in11 x)).getD i false = (run (gs2.map (dropGate 10)) (List.ofFn x)).getD (drop 10 i) false := by
        apply drop_sim 10 gs2 (in11 x) (List.ofFn x)
          (by rw [in11_len, List.length_ofFn]) (by rw [List.length_ofFn]) hno10
        intro i hi
        by_cases hlt : i < 10
        · have hdi : drop 10 i = i := by dsimp only [drop]; split_ifs; rfl
          rw [hdi, in11_lt x i hlt, List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hlt),
              List.getElem_ofFn]
        · have hdi : drop 10 i = i - 1 := by dsimp only [drop]; split_ifs; omega
          rw [hdi, List.getD_eq_default (in11 x) _ (by rw [in11_len]; omega),
              List.getD_eq_default (List.ofFn x) _ (by rw [List.length_ofFn]; omega)]
      change (run (gs2.map (dropGate 10) ++ [⟨GateOp.and, [drop 10 u2, drop 10 v2]⟩]) (List.ofFn x)).getD (10 + gs2.length) false = P10 x
      rw [run_append]
      have hl : 10 + gs2.length = (run (gs2.map (dropGate 10)) (List.ofFn x)).length := by
        rw [run_len, List.length_ofFn, List.length_map]
      simp only [run, List.foldl_cons, List.foldl_nil, step, hl, getD_snoc_end,
        List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id, Bool.and_true]
      rw [← hsim u2 hu2_ne10, ← hsim v2 hv2_ne10]
      exact hD2_exact x
  let lift (y : Fin 9 → Bool) : Fin 10 → Bool :=
    ![false, y 6, y 8, y 5, y 7, y 4, y 1, y 3, y 0, y 2]
  have hP10_lift (y : Fin 9 → Bool) : P10 (lift y) = P9 y := by
    change (false && y 6 || y 6 && y 8 || y 8 && y 5 || y 5 && y 7 || y 7 && false ||
            false && y 4 || y 6 && y 1 || y 8 && y 3 || y 5 && y 0 || y 7 && y 2 ||
            y 4 && y 3 || y 3 && y 2 || y 2 && y 1 || y 1 && y 0 || y 0 && y 4) =
           (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 ||
            y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 ||
            y 5 && y 7 || y 6 && y 8 || y 8 && y 5)
    simp only [Bool.false_and, Bool.false_or,
      Bool.and_comm, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]
  let elimGate (st : List (Bool ⊕ ℕ)) (outIdx : ℕ) (g : Gate) : (Bool ⊕ ℕ) × Option Gate :=
    let ins := g.inputs.map (fun i => st.getD i (Sum.inl false))
    GateOp.casesOn g.op
      (List.casesOn ins
        (Sum.inl true, none)
        (fun a rest => List.casesOn rest
          (a, none)
          (fun b _ => Sum.elim
            (fun ba => Bool.casesOn ba (Sum.inl false, none) (b, none))
            (fun ka => Sum.elim
              (fun bb => Bool.casesOn bb (Sum.inl false, none) (Sum.inr ka, none))
              (fun kb => (Sum.inr outIdx, some ⟨GateOp.and, [ka, kb]⟩)) b) a)))
      (List.casesOn ins
        (Sum.inl false, none)
        (fun a rest => List.casesOn rest
          (a, none)
          (fun b _ => Sum.elim
            (fun ba => Bool.casesOn ba (b, none) (Sum.inl true, none))
            (fun ka => Sum.elim
              (fun bb => Bool.casesOn bb (Sum.inr ka, none) (Sum.inl true, none))
              (fun kb => (Sum.inr outIdx, some ⟨GateOp.or, [ka, kb]⟩)) b) a)))
      (List.casesOn ins
        (Sum.inl true, none)
        (fun a _ => Sum.elim
          (fun ba => (Sum.inl (!ba), none))
          (fun ka => (Sum.inr outIdx, some ⟨GateOp.not, [ka]⟩)) a))
      (fun _ => (Sum.inl false, none))
      (Sum.inl false, none)
  let elimStep (acc : List (Bool ⊕ ℕ) × List Gate × List Bool) (g : Gate) :
      List (Bool ⊕ ℕ) × List Gate × List Bool :=
    let r := elimGate acc.1 (9 + acc.2.1.length) g
    (acc.1 ++ [r.1], Option.elim r.2 acc.2.1 (fun g' => acc.2.1 ++ [g']), acc.2.2 ++ [r.2.isSome])
  let st0 : List (Bool ⊕ ℕ) :=
    [Sum.inl false, Sum.inr 6, Sum.inr 8, Sum.inr 5, Sum.inr 7,
     Sum.inr 4, Sum.inr 1, Sum.inr 3, Sum.inr 0, Sum.inr 2, Sum.inl true]
  have hst0_agree (y : Fin 9 → Bool) (i : ℕ) (hi : i < 11) :
      evalSym (st0.getD i (Sum.inl false)) (List.ofFn y) = (in11 (lift y)).getD i false := by
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
        i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [in11_0]; rfl
    · rw [in11_lt (lift y) 1 (by omega)]; simp [st0, evalSym, lift]
    · rw [in11_lt (lift y) 2 (by omega)]; simp [st0, evalSym, lift]
    · rw [in11_lt (lift y) 3 (by omega)]; simp [st0, evalSym, lift]
    · rw [in11_lt (lift y) 4 (by omega)]; simp [st0, evalSym, lift]
    · rw [in11_lt (lift y) 5 (by omega)]; simp [st0, evalSym, lift]
    · rw [in11_lt (lift y) 6 (by omega)]; simp [st0, evalSym, lift]
    · rw [in11_lt (lift y) 7 (by omega)]; simp [st0, evalSym, lift]
    · rw [in11_lt (lift y) 8 (by omega)]; simp [st0, evalSym, lift]
    · rw [in11_lt (lift y) 9 (by omega)]; simp [st0, evalSym, lift]
    · rw [in11_10]; rfl
  have elim_fold (gs_in : List Gate) :
      ∀ (st : List (Bool ⊕ ℕ)) (gs_out : List Gate) (fl : List Bool) (gs_done : List Gate),
        (∀ g ∈ gs_in, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
        st.length = 11 + gs_done.length →
        fl.length = gs_done.length →
        gs_out.length = fl.count true →
        (∀ g ∈ gs_out, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
        (∀ s ∈ st, Sum.elim (fun _ => True) (fun k => k < 9 + gs_out.length) s) →
        (∀ (y : Fin 9 → Bool) (i : ℕ), i < st.length →
          evalSym (st.getD i (Sum.inl false)) (run gs_out (List.ofFn y)) =
            (run gs_done (in11 (lift y))).getD i false) →
        let res := gs_in.foldl elimStep (st, gs_out, fl)
        res.1.length = 11 + (gs_done ++ gs_in).length ∧
        res.2.2.length = (gs_done ++ gs_in).length ∧
        res.2.1.length = res.2.2.count true ∧
        (∀ g ∈ res.2.1, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
        (∀ i < st.length, res.1.getD i (Sum.inl false) = st.getD i (Sum.inl false)) ∧
        (∀ j < fl.length, res.2.2.getD j false = fl.getD j false) ∧
        (∀ j < gs_in.length,
          let g := gs_in.getD j ⟨GateOp.or, []⟩
          (∀ i ∈ g.inputs, i < 11 + gs_done.length + j) →
          let r := elimGate res.1 (9 + gs_out.length) g
          (res.2.2.getD (gs_done.length + j) false = r.2.isSome) ∧
          (∀ c : Bool, r.1 = Sum.inl c → res.1.getD (11 + gs_done.length + j) (Sum.inl false) = Sum.inl c)) ∧
        (∀ (y : Fin 9 → Bool) (i : ℕ), i < res.1.length →
          evalSym (res.1.getD i (Sum.inl false)) (run res.2.1 (List.ofFn y)) =
            (run (gs_done ++ gs_in) (in11 (lift y))).getD i false) := by
    induction gs_in with
    | nil =>
      intro st gs_out fl gs_done _ hst hfl hcnt hfan_out _ hag
      simp only [List.foldl_nil, List.append_nil, List.length_nil]
      exact ⟨hst, hfl, hcnt, hfan_out, fun _ _ => trivial, fun _ _ => trivial, fun j hj => by omega, hag⟩
    | cons g rest ih =>
      intro st gs_out fl gs_done hfin hst hfl hcnt hfan_out hbd hag
      have hgfan := hfin g List.mem_cons_self
      have hrest_fin : ∀ g' ∈ rest, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
        fun g' hm => hfin g' (List.mem_cons_of_mem _ hm)
      have hget_bd (i : ℕ) : Sum.elim (fun _ => True) (fun k => k < 9 + gs_out.length) (st.getD i (Sum.inl false)) := by
        by_cases hi : i < st.length
        · rw [List.getD_eq_getElem _ _ hi]
          exact hbd _ (List.getElem_mem hi)
        · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
          trivial
      have hval (y : Fin 9 → Bool) (i : ℕ) :
          evalSym (st.getD i (Sum.inl false)) (run gs_out (List.ofFn y)) =
            (run gs_done (in11 (lift y))).getD i false := by
        by_cases hi : i < st.length
        · exact hag y i hi
        · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi),
              List.getD_eq_default _ _ (by rw [run_len, in11_len]; omega)]
          rfl
      let r := elimGate st (9 + gs_out.length) g
      let st1 := st ++ [r.1]
      let gs1 := Option.elim r.2 gs_out (fun g' => gs_out ++ [g'])
      let fl1 := fl ++ [r.2.isSome]
      have hstep_ok :
          gs1.length = fl1.count true ∧
          (∀ g' ∈ gs1, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2) ∧
          Sum.elim (fun _ => True) (fun k => k < 9 + gs1.length) r.1 ∧
          (∀ y : Fin 9 → Bool,
            evalSym r.1 (run gs1 (List.ofFn y)) =
              g.op.eval (g.inputs.map fun i => (run gs_done (in11 (lift y))).getD i false)) := by
        have hcnt_none (hr : r.2 = none) : gs1.length = fl1.count true := by
          simp only [gs1, fl1, hr, Option.elim_none, Option.isSome_none,
            List.count_append, List.count_cons, List.count_nil, hcnt]
          rfl
        have hcnt_some (g' : Gate) (hr : r.2 = some g') : gs1.length = fl1.count true := by
          simp only [gs1, fl1, hr, Option.elim_some, Option.isSome_some,
            List.length_append, List.length_cons, List.length_nil,
            List.count_append, List.count_cons, List.count_nil, hcnt, beq_self_eq_true, ↓reduceIte]
        rcases hgfan.1 with hop | hop | hop
        · change g.op = GateOp.and at hop
          cases hgi : g.inputs with
          | nil =>
            have hr2 : r.2 = none := by simp only [r, elimGate, hop, hgi, List.map_nil]
            refine ⟨hcnt_none hr2, by simp only [gs1, hr2, Option.elim_none]; exact hfan_out,
              by simp only [r, elimGate, hop, hgi, List.map_nil]; trivial, fun _ => by
                simp only [r, gs1, elimGate, hop, hgi, List.map_nil, Option.elim_none, eval_and, List.all_nil, evalSym, Sum.elim_inl, id]⟩
          | cons i1 t1 =>
            cases t1 with
            | nil =>
              have hr2 : r.2 = none := by simp only [r, elimGate, hop, hgi, List.map_cons, List.map_nil]
              have hr1 : r.1 = st.getD i1 (Sum.inl false) := by simp only [r, elimGate, hop, hgi, List.map_cons, List.map_nil]
              refine ⟨hcnt_none hr2, by simp only [gs1, hr2, Option.elim_none]; exact hfan_out,
                by rw [hr1]; simp only [gs1, hr2, Option.elim_none]; exact hget_bd i1, fun y => ?_⟩
              simp only [gs1, hr2, Option.elim_none, hr1, hop, List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id, Bool.and_true]
              exact hval y i1
            | cons i2 t2 =>
              cases t2 with
              | nil =>
                have hb1 := hget_bd i1
                have hb2 := hget_bd i2
                cases hs1 : st.getD i1 (Sum.inl false) with
                | inl b1 =>
                  cases b1
                  · have hr : r = (Sum.inl false, none) := by
                      simp only [r, elimGate, hop, hgi, List.map_cons, List.map_nil, hs1, Sum.elim_inl]
                    refine ⟨hcnt_none (by rw [hr]), by simp only [gs1, hr, Option.elim_none]; exact hfan_out,
                      by simp only [hr]; trivial, fun y => ?_⟩
                    have hv1 := hval y i1; rw [hs1] at hv1
                    simp only [evalSym, Sum.elim_inl, id] at hv1
                    simp only [gs1, hr, Option.elim_none, evalSym, Sum.elim_inl, id, hop,
                      List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, Bool.and_true, ← hv1, Bool.false_and]
                  · have hr : r = (st.getD i2 (Sum.inl false), none) := by
                      simp only [r, elimGate, hop, hgi, List.map_cons, List.map_nil, hs1, Sum.elim_inl]
                    refine ⟨hcnt_none (by rw [hr]), by simp only [gs1, hr, Option.elim_none]; exact hfan_out,
                      by simp only [gs1, hr, Option.elim_none]; exact hb2, fun y => ?_⟩
                    have hv1 := hval y i1; rw [hs1] at hv1
                    simp only [evalSym, Sum.elim_inl, id] at hv1
                    simp only [gs1, hr, Option.elim_none, hop, List.map_cons, List.map_nil,
                      eval_and, List.all_cons, List.all_nil, id, Bool.and_true, ← hv1, Bool.true_and]
                    exact hval y i2
                | inr ka =>
                  cases hs2 : st.getD i2 (Sum.inl false) with
                  | inl b2 =>
                    cases b2
                    · have hr : r = (Sum.inl false, none) := by
                        simp only [r, elimGate, hop, hgi, List.map_cons, List.map_nil, hs1, hs2, Sum.elim_inr, Sum.elim_inl]
                      refine ⟨hcnt_none (by rw [hr]), by simp only [gs1, hr, Option.elim_none]; exact hfan_out,
                        by simp only [hr]; trivial, fun y => ?_⟩
                      have hv2 := hval y i2; rw [hs2] at hv2
                      simp only [evalSym, Sum.elim_inl, id] at hv2
                      simp only [gs1, hr, Option.elim_none, evalSym, Sum.elim_inl, id, hop,
                        List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, Bool.and_true, ← hv2, Bool.and_false]
                    · have hr : r = (Sum.inr ka, none) := by
                        simp only [r, elimGate, hop, hgi, List.map_cons, List.map_nil, hs1, hs2, Sum.elim_inr, Sum.elim_inl]
                      refine ⟨hcnt_none (by rw [hr]), by simp only [gs1, hr, Option.elim_none]; exact hfan_out,
                        by simp only [gs1, hr, Option.elim_none]; rw [← hs1]; exact hb1, fun y => ?_⟩
                      have hv1 := hval y i1; rw [hs1] at hv1
                      have hv2 := hval y i2; rw [hs2] at hv2
                      simp only [evalSym, Sum.elim_inl, id] at hv2
                      simp only [gs1, hr, Option.elim_none, hop, List.map_cons, List.map_nil,
                        eval_and, List.all_cons, List.all_nil, id, Bool.and_true, ← hv2, ← hv1]
                  | inr kb =>
                    have hr : r = (Sum.inr (9 + gs_out.length), some ⟨GateOp.and, [ka, kb]⟩) := by
                      simp only [r, elimGate, hop, hgi, List.map_cons, List.map_nil, hs1, hs2, Sum.elim_inr]
                    refine ⟨hcnt_some _ (by rw [hr]), ?_,
                      by simp only [gs1, hr, Option.elim_some, Sum.elim_inr, List.length_append, List.length_cons, List.length_nil]; omega,
                      fun y => ?_⟩
                    · intro g' hm
                      simp only [gs1, hr, Option.elim_some, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
                      rcases hm with hm | rfl
                      · exact hfan_out g' hm
                      · exact ⟨Or.inl rfl, by simp⟩
                    · simp only [gs1, hr, Option.elim_some, evalSym, Sum.elim_inr, run_append]
                      have hl : 9 + gs_out.length = (run gs_out (List.ofFn y)).length := by
                        rw [run_len, List.length_ofFn]
                      simp only [run, List.foldl_cons, List.foldl_nil, step, hl, getD_snoc_end,
                        hop, List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id, Bool.and_true]
                      have hv1 := hval y i1; rw [hs1] at hv1
                      have hv2 := hval y i2; rw [hs2] at hv2
                      simp only [evalSym, Sum.elim_inr] at hv1 hv2
                      rw [hv1, hv2]
              | cons _ _ => have := hgfan.2; rw [hgi] at this; simp at this
        · change g.op = GateOp.or at hop
          cases hgi : g.inputs with
          | nil =>
            have hr2 : r.2 = none := by simp only [r, elimGate, hop, hgi, List.map_nil]
            refine ⟨hcnt_none hr2, by simp only [gs1, hr2, Option.elim_none]; exact hfan_out,
              by simp only [r, elimGate, hop, hgi, List.map_nil]; trivial, fun _ => by
                simp only [r, gs1, elimGate, hop, hgi, List.map_nil, Option.elim_none, eval_or, List.any_nil, evalSym, Sum.elim_inl, id]⟩
          | cons i1 t1 =>
            cases t1 with
            | nil =>
              have hr2 : r.2 = none := by simp only [r, elimGate, hop, hgi, List.map_cons, List.map_nil]
              have hr1 : r.1 = st.getD i1 (Sum.inl false) := by simp only [r, elimGate, hop, hgi, List.map_cons, List.map_nil]
              refine ⟨hcnt_none hr2, by simp only [gs1, hr2, Option.elim_none]; exact hfan_out,
                by rw [hr1]; simp only [gs1, hr2, Option.elim_none]; exact hget_bd i1, fun y => ?_⟩
              simp only [gs1, hr2, Option.elim_none, hr1, hop, List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id, Bool.or_false]
              exact hval y i1
            | cons i2 t2 =>
              cases t2 with
              | nil =>
                have hb1 := hget_bd i1
                have hb2 := hget_bd i2
                cases hs1 : st.getD i1 (Sum.inl false) with
                | inl b1 =>
                  cases b1
                  · have hr : r = (st.getD i2 (Sum.inl false), none) := by
                      simp only [r, elimGate, hop, hgi, List.map_cons, List.map_nil, hs1, Sum.elim_inl]
                    refine ⟨hcnt_none (by rw [hr]), by simp only [gs1, hr, Option.elim_none]; exact hfan_out,
                      by simp only [gs1, hr, Option.elim_none]; exact hb2, fun y => ?_⟩
                    have hv1 := hval y i1; rw [hs1] at hv1
                    simp only [evalSym, Sum.elim_inl, id] at hv1
                    simp only [gs1, hr, Option.elim_none, hop, List.map_cons, List.map_nil,
                      eval_or, List.any_cons, List.any_nil, id, Bool.or_false, ← hv1, Bool.false_or]
                    exact hval y i2
                  · have hr : r = (Sum.inl true, none) := by
                      simp only [r, elimGate, hop, hgi, List.map_cons, List.map_nil, hs1, Sum.elim_inl]
                    refine ⟨hcnt_none (by rw [hr]), by simp only [gs1, hr, Option.elim_none]; exact hfan_out,
                      by simp only [hr]; trivial, fun y => ?_⟩
                    have hv1 := hval y i1; rw [hs1] at hv1
                    simp only [evalSym, Sum.elim_inl, id] at hv1
                    simp only [gs1, hr, Option.elim_none, evalSym, Sum.elim_inl, id, hop,
                      List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, Bool.or_false, ← hv1, Bool.true_or]
                | inr ka =>
                  cases hs2 : st.getD i2 (Sum.inl false) with
                  | inl b2 =>
                    cases b2
                    · have hr : r = (Sum.inr ka, none) := by
                        simp only [r, elimGate, hop, hgi, List.map_cons, List.map_nil, hs1, hs2, Sum.elim_inr, Sum.elim_inl]
                      refine ⟨hcnt_none (by rw [hr]), by simp only [gs1, hr, Option.elim_none]; exact hfan_out,
                        by simp only [gs1, hr, Option.elim_none]; rw [← hs1]; exact hb1, fun y => ?_⟩
                      have hv1 := hval y i1; rw [hs1] at hv1
                      have hv2 := hval y i2; rw [hs2] at hv2
                      simp only [evalSym, Sum.elim_inl, id] at hv2
                      simp only [gs1, hr, Option.elim_none, hop, List.map_cons, List.map_nil,
                        eval_or, List.any_cons, List.any_nil, id, Bool.or_false, ← hv2, ← hv1]
                    · have hr : r = (Sum.inl true, none) := by
                        simp only [r, elimGate, hop, hgi, List.map_cons, List.map_nil, hs1, hs2, Sum.elim_inr, Sum.elim_inl]
                      refine ⟨hcnt_none (by rw [hr]), by simp only [gs1, hr, Option.elim_none]; exact hfan_out,
                        by simp only [hr]; trivial, fun y => ?_⟩
                      have hv2 := hval y i2; rw [hs2] at hv2
                      simp only [evalSym, Sum.elim_inl, id] at hv2
                      simp only [gs1, hr, Option.elim_none, evalSym, Sum.elim_inl, id, hop,
                        List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, Bool.or_false, ← hv2, Bool.or_true]
                  | inr kb =>
                    have hr : r = (Sum.inr (9 + gs_out.length), some ⟨GateOp.or, [ka, kb]⟩) := by
                      simp only [r, elimGate, hop, hgi, List.map_cons, List.map_nil, hs1, hs2, Sum.elim_inr]
                    refine ⟨hcnt_some _ (by rw [hr]), ?_,
                      by simp only [gs1, hr, Option.elim_some, Sum.elim_inr, List.length_append, List.length_cons, List.length_nil]; omega,
                      fun y => ?_⟩
                    · intro g' hm
                      simp only [gs1, hr, Option.elim_some, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
                      rcases hm with hm | rfl
                      · exact hfan_out g' hm
                      · exact ⟨Or.inr (Or.inl rfl), by simp⟩
                    · simp only [gs1, hr, Option.elim_some, evalSym, Sum.elim_inr, run_append]
                      have hl : 9 + gs_out.length = (run gs_out (List.ofFn y)).length := by
                        rw [run_len, List.length_ofFn]
                      simp only [run, List.foldl_cons, List.foldl_nil, step, hl, getD_snoc_end,
                        hop, List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id, Bool.or_false]
                      have hv1 := hval y i1; rw [hs1] at hv1
                      have hv2 := hval y i2; rw [hs2] at hv2
                      simp only [evalSym, Sum.elim_inr] at hv1 hv2
                      rw [hv1, hv2]
              | cons _ _ => have := hgfan.2; rw [hgi] at this; simp at this
        · change g.op = GateOp.not at hop
          cases hgi : g.inputs with
          | nil =>
            have hr2 : r.2 = none := by simp only [r, elimGate, hop, hgi, List.map_nil]
            refine ⟨hcnt_none hr2, by simp only [gs1, hr2, Option.elim_none]; exact hfan_out,
              by simp only [r, elimGate, hop, hgi, List.map_nil]; trivial, fun _ => by
                simp only [r, gs1, elimGate, hop, hgi, List.map_nil, Option.elim_none, eval_not, List.headD_nil, evalSym, Sum.elim_inl, id, Bool.not_false]⟩
          | cons i1 t1 =>
            cases hs1 : st.getD i1 (Sum.inl false) with
            | inl b1 =>
              have hr : r = (Sum.inl (!b1), none) := by
                simp only [r, elimGate, hop, hgi, List.map_cons, hs1, Sum.elim_inl]
              refine ⟨hcnt_none (by rw [hr]), by simp only [gs1, hr, Option.elim_none]; exact hfan_out,
                by simp only [hr]; trivial, fun y => ?_⟩
              have hv1 := hval y i1; rw [hs1] at hv1
              simp only [evalSym, Sum.elim_inl, id] at hv1
              simp only [gs1, hr, Option.elim_none, evalSym, Sum.elim_inl, id, hop,
                List.map_cons, eval_not, List.headD_cons, hv1]
            | inr ka =>
              have hr : r = (Sum.inr (9 + gs_out.length), some ⟨GateOp.not, [ka]⟩) := by
                simp only [r, elimGate, hop, hgi, List.map_cons, hs1, Sum.elim_inr]
              refine ⟨hcnt_some _ (by rw [hr]), ?_,
                by simp only [gs1, hr, Option.elim_some, Sum.elim_inr, List.length_append, List.length_cons, List.length_nil]; omega,
                fun y => ?_⟩
              · intro g' hm
                simp only [gs1, hr, Option.elim_some, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
                rcases hm with hm | rfl
                · exact hfan_out g' hm
                · exact ⟨Or.inr (Or.inr rfl), by simp⟩
              · simp only [gs1, hr, Option.elim_some, evalSym, Sum.elim_inr, run_append]
                have hl : 9 + gs_out.length = (run gs_out (List.ofFn y)).length := by
                  rw [run_len, List.length_ofFn]
                simp only [run, List.foldl_cons, List.foldl_nil, step, hl, getD_snoc_end,
                  hop, List.map_cons, List.map_nil, eval_not, List.headD_cons]
                have hv1 := hval y i1; rw [hs1] at hv1
                simp only [evalSym, Sum.elim_inr] at hv1
                rw [hv1]
      have hgs1_ge : gs_out.length ≤ gs1.length := by
        dsimp only [gs1]
        cases r.2 with
        | none => exact Nat.le_refl _
        | some g' => simp only [Option.elim_some, List.length_append, List.length_cons, List.length_nil]; omega
      have hkeep_old (y : Fin 9 → Bool) (s : Bool ⊕ ℕ)
          (hs : Sum.elim (fun _ => True) (fun k => k < 9 + gs_out.length) s) :
          evalSym s (run gs1 (List.ofFn y)) = evalSym s (run gs_out (List.ofFn y)) := by
        cases s with
        | inl _ => rfl
        | inr k =>
          simp only [Sum.elim_inr] at hs
          dsimp only [gs1]
          cases r.2 with
          | none => rfl
          | some g' =>
            simp only [Option.elim_some, evalSym, Sum.elim_inr, run_append]
            exact run_keep [g'] (run gs_out (List.ofFn y)) k (by rw [run_len, List.length_ofFn]; exact hs)
      have hres := ih st1 gs1 fl1 (gs_done ++ [g]) hrest_fin
        (by simp only [st1, List.length_append, List.length_cons, List.length_nil]; omega)
        (by simp only [fl1, List.length_append, List.length_cons, List.length_nil]; omega)
        hstep_ok.1 hstep_ok.2.1
        (by
          intro s hm
          simp only [st1, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
          rcases hm with hm | rfl
          · cases s with
            | inl _ => trivial
            | inr k =>
              have hk := hbd (Sum.inr k) hm
              simp only [Sum.elim_inr] at hk ⊢
              omega
          · exact hstep_ok.2.2.1)
        (by
          intro y i hi
          simp only [st1, List.length_append, List.length_cons, List.length_nil] at hi
          rw [run_append]
          change evalSym (st1.getD i (Sum.inl false)) (run gs1 (List.ofFn y)) =
            (step (run gs_done (in11 (lift y))) g).getD i false
          by_cases hlt : i < st.length
          · rw [List.getD_append _ _ _ _ hlt]
            have hne : i ≠ (run gs_done (in11 (lift y))).length := by rw [run_len, in11_len]; omega
            rw [getD_snoc_ne _ _ _ hne, hkeep_old y _ (hget_bd i)]
            exact hag y i hlt
          · have hieq : i = st.length := by omega
            subst hieq
            have hget : st1.getD st.length (Sum.inl false) = r.1 := by
              simp only [st1, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
                Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            have hlen : st.length = (run gs_done (in11 (lift y))).length := by rw [run_len, in11_len, hst]
            rw [hget, hlen, getD_snoc_end]
            exact hstep_ok.2.2.2 y)
      have heG_out_indep (sL : List (Bool ⊕ ℕ)) (o1 o2 : ℕ) (gx : Gate) :
          (elimGate sL o1 gx).2.isSome = (elimGate sL o2 gx).2.isSome ∧
          (∀ c : Bool, (elimGate sL o1 gx).1 = Sum.inl c ↔ (elimGate sL o2 gx).1 = Sum.inl c) := by
        dsimp only [elimGate]
        cases gx.op
        · cases gx.inputs.map (fun i => sL.getD i (Sum.inl false)) with
          | nil => exact ⟨rfl, fun _ => Iff.rfl⟩
          | cons a rest1 =>
            cases rest1 with
            | nil => exact ⟨rfl, fun _ => Iff.rfl⟩
            | cons b _ =>
              cases a with
              | inl ba => cases ba <;> exact ⟨rfl, fun _ => Iff.rfl⟩
              | inr ka =>
                cases b with
                | inl bb => cases bb <;> exact ⟨rfl, fun _ => Iff.rfl⟩
                | inr kb => exact ⟨rfl, fun _ => ⟨fun h => (by cases h), fun h => (by cases h)⟩⟩
        · cases gx.inputs.map (fun i => sL.getD i (Sum.inl false)) with
          | nil => exact ⟨rfl, fun _ => Iff.rfl⟩
          | cons a rest1 =>
            cases rest1 with
            | nil => exact ⟨rfl, fun _ => Iff.rfl⟩
            | cons b _ =>
              cases a with
              | inl ba => cases ba <;> exact ⟨rfl, fun _ => Iff.rfl⟩
              | inr ka =>
                cases b with
                | inl bb => cases bb <;> exact ⟨rfl, fun _ => Iff.rfl⟩
                | inr kb => exact ⟨rfl, fun _ => ⟨fun h => (by cases h), fun h => (by cases h)⟩⟩
        · cases gx.inputs.map (fun i => sL.getD i (Sum.inl false)) with
          | nil => exact ⟨rfl, fun _ => Iff.rfl⟩
          | cons a _ =>
            cases a with
            | inl ba => exact ⟨rfl, fun _ => Iff.rfl⟩
            | inr ka => exact ⟨rfl, fun _ => ⟨fun h => (by cases h), fun h => (by cases h)⟩⟩
        · exact ⟨rfl, fun _ => Iff.rfl⟩
        · exact ⟨rfl, fun _ => Iff.rfl⟩
      rw [List.append_assoc, List.singleton_append] at hres
      dsimp only
      have hfold : (g :: rest).foldl elimStep (st, gs_out, fl) = rest.foldl elimStep (st1, gs1, fl1) := rfl
      rw [hfold]
      refine ⟨hres.1, hres.2.1, hres.2.2.1, hres.2.2.2.1, ?_, ?_, ?_, hres.2.2.2.2.2.2.2⟩
      · intro i hi
        rw [hres.2.2.2.2.1 i (by simp only [st1, List.length_append, List.length_cons, List.length_nil]; omega)]
        exact List.getD_append _ _ _ _ hi
      · intro j hj
        rw [hres.2.2.2.2.2.1 j (by simp only [fl1, List.length_append, List.length_cons, List.length_nil]; omega)]
        exact List.getD_append _ _ _ _ hj
      · intro j hj hinb
        cases j with
        | zero =>
          change ∀ i ∈ g.inputs, i < 11 + gs_done.length + 0 at hinb
          have hst_agree : ∀ i ∈ g.inputs,
              (rest.foldl elimStep (st1, gs1, fl1)).1.getD i (Sum.inl false) = st.getD i (Sum.inl false) := by
            intro i hi
            have hilt : i < st.length := by have := hinb i hi; omega
            rw [hres.2.2.2.2.1 i (by simp only [st1, List.length_append, List.length_cons, List.length_nil]; omega)]
            exact List.getD_append _ _ _ _ hilt
          have hmap_eq : g.inputs.map (fun i => (rest.foldl elimStep (st1, gs1, fl1)).1.getD i (Sum.inl false)) =
              g.inputs.map (fun i => st.getD i (Sum.inl false)) := List.map_congr_left hst_agree
          have heg_eq : elimGate (rest.foldl elimStep (st1, gs1, fl1)).1 (9 + gs_out.length) g = r := by
            dsimp only [r, elimGate]
            rw [hmap_eq]
          change ((rest.foldl elimStep (st1, gs1, fl1)).2.2.getD (gs_done.length + 0) false =
              (elimGate (rest.foldl elimStep (st1, gs1, fl1)).1 (9 + gs_out.length) g).2.isSome) ∧
            (∀ c : Bool, (elimGate (rest.foldl elimStep (st1, gs1, fl1)).1 (9 + gs_out.length) g).1 = Sum.inl c →
              (rest.foldl elimStep (st1, gs1, fl1)).1.getD (11 + gs_done.length + 0) (Sum.inl false) = Sum.inl c)
          rw [heg_eq]
          refine ⟨?_, ?_⟩
          · rw [Nat.add_zero, hres.2.2.2.2.2.1 gs_done.length (by simp only [fl1, List.length_append, List.length_cons, List.length_nil]; omega)]
            simp only [fl1, ← hfl, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
              Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
          · intro c hc
            rw [Nat.add_zero, hres.2.2.2.2.1 (11 + gs_done.length) (by simp only [st1, List.length_append, List.length_cons, List.length_nil]; omega)]
            rw [← hst]
            simp only [st1, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
              Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, hc]
        | succ j' =>
          change ∀ i ∈ (rest.getD j' ⟨GateOp.or, []⟩).inputs, i < 11 + gs_done.length + (j' + 1) at hinb
          have hj' : j' < rest.length := by simp only [List.length_cons] at hj; omega
          have hsub := hres.2.2.2.2.2.2.1 j' hj' (by
            intro i hi
            have := hinb i hi
            simp only [List.length_append, List.length_cons, List.length_nil] at *
            omega)
          have hidx1 : (gs_done ++ [g]).length + j' = gs_done.length + (j' + 1) := by
            simp only [List.length_append, List.length_cons, List.length_nil]; omega
          have hidx2 : 11 + (gs_done ++ [g]).length + j' = 11 + gs_done.length + (j' + 1) := by
            simp only [List.length_append, List.length_cons, List.length_nil]; omega
          rw [hidx1, hidx2] at hsub
          have hindep := heG_out_indep (rest.foldl elimStep (st1, gs1, fl1)).1 (9 + gs1.length) (9 + gs_out.length) (rest.getD j' ⟨GateOp.or, []⟩)
          change ((rest.foldl elimStep (st1, gs1, fl1)).2.2.getD (gs_done.length + (j' + 1)) false =
              (elimGate (rest.foldl elimStep (st1, gs1, fl1)).1 (9 + gs_out.length) (rest.getD j' ⟨GateOp.or, []⟩)).2.isSome) ∧
            (∀ c : Bool, (elimGate (rest.foldl elimStep (st1, gs1, fl1)).1 (9 + gs_out.length) (rest.getD j' ⟨GateOp.or, []⟩)).1 = Sum.inl c →
              (rest.foldl elimStep (st1, gs1, fl1)).1.getD (11 + gs_done.length + (j' + 1)) (Sum.inl false) = Sum.inl c)
          refine ⟨hsub.1.trans hindep.1, fun c hc => hsub.2 c ((hindep.2 c).mpr hc)⟩
  have helim := elim_fold gs2 st0 [] [] [] hD2_fan rfl rfl rfl (by intro _ h; cases h)
    (by
      intro s hm
      simp only [st0, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | trivial | (simp only [Sum.elim_inr, List.length_nil, Nat.add_zero]; omega))
    (by
      intro y i hi
      simp only [st0, List.length_cons, List.length_nil] at hi
      exact hst0_agree y i hi)
  simp only [List.nil_append, Nat.zero_add, List.length_nil] at helim
  let res0 := gs2.foldl elimStep (st0, [], [])
  let stF := res0.1
  let gs0 := res0.2.1
  let flF := res0.2.2
  have hstF_len : stF.length = 11 + gs2.length := helim.1
  have hflF_len : flF.length = gs2.length := helim.2.1
  have hgs0_cnt : gs0.length = flF.count true := helim.2.2.1
  have hgs0_fan : ∀ g ∈ gs0, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
    helim.2.2.2.1
  have hstF_0 : stF.getD 0 (Sum.inl false) = Sum.inl false :=
    helim.2.2.2.2.1 0 (by simp [st0])
  have hstF_10 : stF.getD 10 (Sum.inl false) = Sum.inl true :=
    helim.2.2.2.2.1 10 (by simp [st0])
  have hstF_val (y : Fin 9 → Bool) (i : ℕ) (hi : i < 11 + gs2.length) :
      evalSym (stF.getD i (Sum.inl false)) (run gs0 (List.ofFn y)) =
        (D2.wires (in11 (lift y))).getD i false :=
    helim.2.2.2.2.2.2.2 y i (by rw [hstF_len]; exact hi)
  let u0 := stF.getD u2 (Sum.inl false)
  let v0 := stF.getD v2 (Sum.inl false)
  have huv0_P9 (y : Fin 9 → Bool) :
      (evalSym u0 (run gs0 (List.ofFn y)) && evalSym v0 (run gs0 (List.ofFn y))) = P9 y := by
    rw [hstF_val y u2 hu2_lt, hstF_val y v2 hv2_lt, hD2_exact (lift y), hP10_lift y]
  have hu0_ne_false : u0 ≠ Sum.inl false := by
    intro h
    have h1 := huv0_P9 (fun _ => true)
    rw [h] at h1
    simp only [evalSym, Sum.elim_inl, id, Bool.false_and] at h1
    have hP : P9 (fun _ => true) = true := rfl
    rw [hP] at h1; cases h1
  have hv0_ne_false : v0 ≠ Sum.inl false := by
    intro h
    have h1 := huv0_P9 (fun _ => true)
    rw [h] at h1
    simp only [evalSym, Sum.elim_inl, id, Bool.and_false] at h1
    have hP : P9 (fun _ => true) = true := rfl
    rw [hP] at h1; cases h1
  have fromRestrict_const (hle15 : gs0.length ≤ 15)
      (hconst : (∃ b : Bool, u0 = Sum.inl b) ∨ (∃ b : Bool, v0 = Sum.inl b)) : False := by
    rcases hconst with ⟨b, hb⟩ | ⟨b, hb⟩
    · cases b
      · exact hu0_ne_false hb
      · cases hv0 : v0 with
        | inl bv =>
          cases bv
          · exact hv0_ne_false hv0
          · have h1 := huv0_P9 (fun _ => false)
            rw [hb, hv0] at h1
            have hP : P9 (fun _ => false) = false := rfl
            rw [hP] at h1; cases h1
        | inr kv =>
          apply hP9
          refine ⟨⟨gs0, kv⟩, hgs0_fan, hle15, fun y => ?_⟩
          have h1 := huv0_P9 y
          rw [hb, hv0] at h1
          change (run gs0 (List.ofFn y)).getD kv false = P9 y
          simpa only [evalSym, Sum.elim_inl, Sum.elim_inr, id, Bool.true_and] using h1
    · cases b
      · exact hv0_ne_false hb
      · cases hu0 : u0 with
        | inl bu =>
          cases bu
          · exact hu0_ne_false hu0
          · have h1 := huv0_P9 (fun _ => false)
            rw [hu0, hb] at h1
            have hP : P9 (fun _ => false) = false := rfl
            rw [hP] at h1; cases h1
        | inr ku =>
          apply hP9
          refine ⟨⟨gs0, ku⟩, hgs0_fan, hle15, fun y => ?_⟩
          have h1 := huv0_P9 y
          rw [hu0, hb] at h1
          change (run gs0 (List.ofFn y)).getD ku false = P9 y
          simpa only [evalSym, Sum.elim_inl, Sum.elim_inr, id, Bool.and_true] using h1
  have fromRestrict_14 (hle14 : gs0.length ≤ 14) : False := by
    cases hu0 : u0 with
    | inl bu => exact fromRestrict_const (by omega) (Or.inl ⟨bu, hu0⟩)
    | inr ku =>
      cases hv0 : v0 with
      | inl bv => exact fromRestrict_const (by omega) (Or.inr ⟨bv, hv0⟩)
      | inr kv =>
        let E9 : Circuit := ⟨gs0 ++ [⟨GateOp.and, [ku, kv]⟩], 9 + gs0.length⟩
        apply hP9
        refine ⟨E9, ?_, ?_, fun y => ?_⟩
        · intro g hm
          simp only [E9, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
          rcases hm with hm | rfl
          · exact hgs0_fan g hm
          · exact ⟨Or.inl rfl, by simp⟩
        · change E9.gates.length ≤ 15
          dsimp only [E9]
          simp only [List.length_append, List.length_cons, List.length_nil]; omega
        · change (run (gs0 ++ [⟨GateOp.and, [ku, kv]⟩]) (List.ofFn y)).getD (9 + gs0.length) false = P9 y
          rw [run_append]
          have hl : 9 + gs0.length = (run gs0 (List.ofFn y)).length := by
            rw [run_len, List.length_ofFn]
          simp only [run, List.foldl_cons, List.foldl_nil, step, hl, getD_snoc_end,
            List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id, Bool.and_true]
          have h1 := huv0_P9 y
          rw [hu0, hv0] at h1
          exact h1
  have hruleA (j : ℕ) (hj : j < gs2.length)
      (hcin : ∃ i ∈ (gs2.getD j ⟨GateOp.or, []⟩).inputs, ∃ b : Bool, stF.getD i (Sum.inl false) = Sum.inl b) :
      flF.getD j false = false := by
    have hcl := hgs2_clean j hj
    have htr := (helim.2.2.2.2.2.2.1 j hj hcl.2.2.1).1
    rw [htr]
    obtain ⟨i0, hi0, b0, hb0⟩ := hcin
    rcases hcl.1 with hop | hop | hop
    · change (gs2.getD j ⟨GateOp.or, []⟩).op = GateOp.and at hop
      have hlen2 := (hcl.2.2.2.2 (Or.inl hop)).1
      cases hgi : (gs2.getD j ⟨GateOp.or, []⟩).inputs with
      | nil => rw [hgi] at hlen2; simp at hlen2
      | cons i1 t1 =>
        cases t1 with
        | nil => rw [hgi] at hlen2; simp at hlen2
        | cons i2 t2 =>
          cases t2 with
          | nil =>
            rw [hgi] at hi0
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi0
            dsimp only [elimGate]
            rw [hop, hgi]
            simp only [List.map_cons, List.map_nil]
            rcases hi0 with rfl | rfl
            · rw [hb0]; cases b0 <;> rfl
            · rw [hb0]; cases stF.getD i1 (Sum.inl false) with
              | inl b1 => cases b1 <;> rfl
              | inr _ => cases b0 <;> rfl
          | cons _ _ => rw [hgi] at hlen2; simp at hlen2
    · change (gs2.getD j ⟨GateOp.or, []⟩).op = GateOp.or at hop
      have hlen2 := (hcl.2.2.2.2 (Or.inr hop)).1
      cases hgi : (gs2.getD j ⟨GateOp.or, []⟩).inputs with
      | nil => rw [hgi] at hlen2; simp at hlen2
      | cons i1 t1 =>
        cases t1 with
        | nil => rw [hgi] at hlen2; simp at hlen2
        | cons i2 t2 =>
          cases t2 with
          | nil =>
            rw [hgi] at hi0
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi0
            dsimp only [elimGate]
            rw [hop, hgi]
            simp only [List.map_cons, List.map_nil]
            rcases hi0 with rfl | rfl
            · rw [hb0]; cases b0 <;> rfl
            · rw [hb0]; cases stF.getD i1 (Sum.inl false) with
              | inl b1 => cases b1 <;> rfl
              | inr _ => cases b0 <;> rfl
          | cons _ _ => rw [hgi] at hlen2; simp at hlen2
    · change (gs2.getD j ⟨GateOp.or, []⟩).op = GateOp.not at hop
      have hlen1 := (hcl.2.2.2.1 hop).1
      cases hgi : (gs2.getD j ⟨GateOp.or, []⟩).inputs with
      | nil => rw [hgi] at hlen1; simp at hlen1
      | cons i1 t1 =>
        cases t1 with
        | nil =>
          rw [hgi] at hi0
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi0
          subst hi0
          dsimp only [elimGate]
          rw [hop, hgi, List.map_cons, hb0]
          rfl
        | cons _ _ => rw [hgi] at hlen1; simp at hlen1
  have hruleB_and_false (j : ℕ) (hj : j < gs2.length)
      (hop : (gs2.getD j ⟨GateOp.or, []⟩).op = GateOp.and)
      (hin : ∃ i ∈ (gs2.getD j ⟨GateOp.or, []⟩).inputs, stF.getD i (Sum.inl false) = Sum.inl false) :
      stF.getD (11 + j) (Sum.inl false) = Sum.inl false := by
    have hcl := hgs2_clean j hj
    have hlen2 := (hcl.2.2.2.2 (Or.inl hop)).1
    apply (helim.2.2.2.2.2.2.1 j hj hcl.2.2.1).2 false
    obtain ⟨i0, hi0, hb0⟩ := hin
    cases hgi : (gs2.getD j ⟨GateOp.or, []⟩).inputs with
    | nil => rw [hgi] at hlen2; simp at hlen2
    | cons i1 t1 =>
      cases t1 with
      | nil => rw [hgi] at hlen2; simp at hlen2
      | cons i2 t2 =>
        cases t2 with
        | nil =>
          rw [hgi] at hi0
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi0
          dsimp only [elimGate]
          rw [hop, hgi]
          simp only [List.map_cons, List.map_nil]
          rcases hi0 with rfl | rfl
          · rw [hb0]; rfl
          · rw [hb0]; cases stF.getD i1 (Sum.inl false) with
            | inl b1 => cases b1 <;> rfl
            | inr _ => rfl
        | cons _ _ => rw [hgi] at hlen2; simp at hlen2
  have hruleB_or_true (j : ℕ) (hj : j < gs2.length)
      (hop : (gs2.getD j ⟨GateOp.or, []⟩).op = GateOp.or)
      (hin : ∃ i ∈ (gs2.getD j ⟨GateOp.or, []⟩).inputs, stF.getD i (Sum.inl false) = Sum.inl true) :
      stF.getD (11 + j) (Sum.inl false) = Sum.inl true := by
    have hcl := hgs2_clean j hj
    have hlen2 := (hcl.2.2.2.2 (Or.inr hop)).1
    apply (helim.2.2.2.2.2.2.1 j hj hcl.2.2.1).2 true
    obtain ⟨i0, hi0, hb0⟩ := hin
    cases hgi : (gs2.getD j ⟨GateOp.or, []⟩).inputs with
    | nil => rw [hgi] at hlen2; simp at hlen2
    | cons i1 t1 =>
      cases t1 with
      | nil => rw [hgi] at hlen2; simp at hlen2
      | cons i2 t2 =>
        cases t2 with
        | nil =>
          rw [hgi] at hi0
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi0
          dsimp only [elimGate]
          rw [hop, hgi]
          simp only [List.map_cons, List.map_nil]
          rcases hi0 with rfl | rfl
          · rw [hb0]; rfl
          · rw [hb0]; cases stF.getD i1 (Sum.inl false) with
            | inl b1 => cases b1 <;> rfl
            | inr _ => rfl
        | cons _ _ => rw [hgi] at hlen2; simp at hlen2
  have hruleB_both_const (j : ℕ) (hj : j < gs2.length)
      (hbin : (gs2.getD j ⟨GateOp.or, []⟩).op = GateOp.and ∨ (gs2.getD j ⟨GateOp.or, []⟩).op = GateOp.or)
      (hall : ∀ i ∈ (gs2.getD j ⟨GateOp.or, []⟩).inputs, ∃ b : Bool, stF.getD i (Sum.inl false) = Sum.inl b) :
      ∃ c : Bool, stF.getD (11 + j) (Sum.inl false) = Sum.inl c := by
    have hcl := hgs2_clean j hj
    have hlen2 := (hcl.2.2.2.2 hbin).1
    cases hgi : (gs2.getD j ⟨GateOp.or, []⟩).inputs with
    | nil => rw [hgi] at hlen2; simp at hlen2
    | cons i1 t1 =>
      cases t1 with
      | nil => rw [hgi] at hlen2; simp at hlen2
      | cons i2 t2 =>
        cases t2 with
        | nil =>
          obtain ⟨b1, hb1⟩ := hall i1 (by rw [hgi]; exact List.mem_cons_self)
          obtain ⟨b2, hb2⟩ := hall i2 (by rw [hgi]; exact List.mem_cons_of_mem _ List.mem_cons_self)
          rcases hbin with hop | hop
          · refine ⟨b1 && b2, (helim.2.2.2.2.2.2.1 j hj hcl.2.2.1).2 (b1 && b2) ?_⟩
            dsimp only [stF, res0] at hb1 hb2
            dsimp only [elimGate]
            rw [hop, hgi]
            simp only [List.map_cons, List.map_nil, hb1, hb2]
            cases b1 <;> cases b2 <;> rfl
          · refine ⟨b1 || b2, (helim.2.2.2.2.2.2.1 j hj hcl.2.2.1).2 (b1 || b2) ?_⟩
            dsimp only [stF, res0] at hb1 hb2
            dsimp only [elimGate]
            rw [hop, hgi]
            simp only [List.map_cons, List.map_nil, hb1, hb2]
            cases b1 <;> cases b2 <;> rfl
        | cons _ _ => rw [hgi] at hlen2; simp at hlen2
  have count_bool_sum (l : List Bool) : l.count true + l.count false = l.length := by
    induction l with
    | nil => rfl
    | cons b t ih =>
      cases b <;> simp <;> omega
  let P010 : Gate → Bool := fun g => g.inputs.contains (0 : ℕ) || g.inputs.contains (10 : ℕ)
  have hP010_iff (g : Gate) : P010 g = true ↔ (0 : ℕ) ∈ g.inputs ∨ (10 : ℕ) ∈ g.inputs := by
    simp only [P010, Bool.or_eq_true, List.contains_iff_mem]
  have hfilter_mono (gs : List Gate) :
      (gs.filter (fun g => g.inputs.contains (10 : ℕ))).length ≤ (gs.filter P010).length := by
    induction gs with
    | nil => exact Nat.le_refl 0
    | cons g t ih =>
      simp only [List.filter_cons]
      by_cases h10 : g.inputs.contains (10 : ℕ) = true
      · have h010 : P010 g = true := by simp only [P010, h10, Bool.or_true]
        simp only [h10, h010, ↓reduceIte, List.length_cons]
        omega
      · have h10f : g.inputs.contains (10 : ℕ) = false := Bool.eq_false_iff.mpr h10
        simp only [h10f, Bool.false_eq_true, ↓reduceIte]
        cases P010 g <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega
  have hfilter_strict (gs : List Gate) (g0 : Gate) (hg0 : g0 ∈ gs)
      (h0 : (0 : ℕ) ∈ g0.inputs) (h10 : (10 : ℕ) ∉ g0.inputs) :
      (gs.filter (fun g => g.inputs.contains (10 : ℕ))).length + 1 ≤ (gs.filter P010).length := by
    induction gs with
    | nil => cases hg0
    | cons g t ih =>
      simp only [List.filter_cons]
      rcases List.mem_cons.mp hg0 with rfl | hmt
      · have h10f : g0.inputs.contains (10 : ℕ) = false :=
          Bool.eq_false_iff.mpr (fun h => h10 (List.contains_iff_mem.mp h))
        have h010t : P010 g0 = true := (hP010_iff g0).mpr (Or.inl h0)
        simp only [h10f, h010t, Bool.false_eq_true, ↓reduceIte, List.length_cons]
        have := hfilter_mono t
        omega
      · have ih' := ih hmt
        by_cases h10g : g.inputs.contains (10 : ℕ) = true
        · have h010g : P010 g = true := by simp only [P010, h10g, Bool.or_true]
          simp only [h10g, h010g, ↓reduceIte, List.length_cons]; omega
        · have h10f : g.inputs.contains (10 : ℕ) = false := Bool.eq_false_iff.mpr h10g
          simp only [h10f, Bool.false_eq_true, ↓reduceIte]
          cases P010 g <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega
  have filter_le_count_false (gs : List Gate) :
      ∀ (fl : List Bool), fl.length = gs.length →
        (∀ j < gs.length, P010 (gs.getD j ⟨GateOp.or, []⟩) = true → fl.getD j false = false) →
        (gs.filter P010).length ≤ fl.count false := by
    induction gs with
    | nil => intro fl _ _; simp
    | cons g t ih =>
      intro fl hlen himp
      cases fl with
      | nil => simp at hlen
      | cons b ft =>
        simp only [List.length_cons] at hlen
        have ih' := ih ft (by omega) (fun j hj hP => himp (j + 1) (by simp only [List.length_cons]; omega) hP)
        simp only [List.filter_cons, List.count_cons]
        cases hPg : P010 g
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases b <;> simp <;> omega
        · have hb : b = false := himp 0 (by simp) hPg
          rw [hb]
          simp only [↓reduceIte, List.length_cons, beq_self_eq_true]
          omega
  have filter_succ_le_count_false (gs : List Gate) :
      ∀ (fl : List Bool) (j0 : ℕ), fl.length = gs.length →
        (∀ j < gs.length, P010 (gs.getD j ⟨GateOp.or, []⟩) = true → fl.getD j false = false) →
        j0 < gs.length → P010 (gs.getD j0 ⟨GateOp.or, []⟩) = false → fl.getD j0 false = false →
        (gs.filter P010).length + 1 ≤ fl.count false := by
    induction gs with
    | nil => intro _ _ _ _ hj0; simp at hj0
    | cons g t ih =>
      intro fl j0 hlen himp hj0 hP0 hfl0
      cases fl with
      | nil => simp at hlen
      | cons b ft =>
        simp only [List.length_cons] at hlen hj0
        have himp_t : ∀ j < t.length, P010 (t.getD j ⟨GateOp.or, []⟩) = true → ft.getD j false = false :=
          fun j hj hP => himp (j + 1) (by simp only [List.length_cons]; omega) hP
        simp only [List.filter_cons, List.count_cons]
        cases j0 with
        | zero =>
          change P010 g = false at hP0
          change b = false at hfl0
          rw [hP0, hfl0]
          simp only [Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
          have := filter_le_count_false t ft (by omega) himp_t
          omega
        | succ j0' =>
          have ih' := ih ft j0' (by omega) himp_t (by omega) hP0 hfl0
          cases hPg : P010 g
          · simp only [Bool.false_eq_true, ↓reduceIte]
            cases b <;> simp <;> omega
          · have hb : b = false := himp 0 (by simp) hPg
            rw [hb]
            simp only [↓reduceIte, List.length_cons, beq_self_eq_true]
            omega
  have filter_ge_one (gs : List Gate) : ∀ j < gs.length, P010 (gs.getD j ⟨GateOp.or, []⟩) = true →
      1 ≤ (gs.filter P010).length := by
    intro j hj hP
    have hm : gs.getD j ⟨GateOp.or, []⟩ ∈ gs := by
      rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
    have hmf : gs.getD j ⟨GateOp.or, []⟩ ∈ gs.filter P010 := List.mem_filter.mpr ⟨hm, hP⟩
    exact List.length_pos_iff.mpr (List.ne_nil_of_mem hmf)
  have filter_ge_two (gs : List Gate) : ∀ j1 j2 : ℕ, j1 < j2 → j2 < gs.length →
      P010 (gs.getD j1 ⟨GateOp.or, []⟩) = true → P010 (gs.getD j2 ⟨GateOp.or, []⟩) = true →
      2 ≤ (gs.filter P010).length := by
    induction gs with
    | nil => intro _ _ _ h2; simp at h2
    | cons g t ih =>
      intro j1 j2 h12 h2 hP1 hP2
      simp only [List.length_cons] at h2
      simp only [List.filter_cons]
      cases j1 with
      | zero =>
        change P010 g = true at hP1
        rw [hP1]
        simp only [↓reduceIte, List.length_cons]
        cases j2 with
        | zero => omega
        | succ j2' =>
          have := filter_ge_one t j2' (by omega) hP2
          omega
      | succ j1' =>
        cases j2 with
        | zero => omega
        | succ j2' =>
          have ih' := ih j1' j2' (by omega) (by omega) hP1 hP2
          cases P010 g <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega
  have filter_ge_three (gs : List Gate) : ∀ j1 j2 j3 : ℕ, j1 < j2 → j2 < j3 → j3 < gs.length →
      P010 (gs.getD j1 ⟨GateOp.or, []⟩) = true → P010 (gs.getD j2 ⟨GateOp.or, []⟩) = true →
      P010 (gs.getD j3 ⟨GateOp.or, []⟩) = true → 3 ≤ (gs.filter P010).length := by
    induction gs with
    | nil => intro _ _ _ _ _ h3; simp at h3
    | cons g t ih =>
      intro j1 j2 j3 h12 h23 h3 hP1 hP2 hP3
      simp only [List.length_cons] at h3
      simp only [List.filter_cons]
      cases j1 with
      | zero =>
        change P010 g = true at hP1
        rw [hP1]
        simp only [↓reduceIte, List.length_cons]
        cases j2 with
        | zero => omega
        | succ j2' =>
          cases j3 with
          | zero => omega
          | succ j3' =>
            have := filter_ge_two t j2' j3' (by omega) (by omega) hP2 hP3
            omega
      | succ j1' =>
        cases j2 with
        | zero => omega
        | succ j2' =>
          cases j3 with
          | zero => omega
          | succ j3' =>
            have ih' := ih j1' j2' j3' (by omega) (by omega) (by omega) hP1 hP2 hP3
            cases P010 g <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega
  have hP010_elim (j : ℕ) (hj : j < gs2.length) (hP : P010 (gs2.getD j ⟨GateOp.or, []⟩) = true) :
      flF.getD j false = false := by
    apply hruleA j hj
    rcases (hP010_iff _).mp hP with h0 | h10
    · exact ⟨0, h0, false, hstF_0⟩
    · exact ⟨10, h10, true, hstF_10⟩
  have hfl_sum : gs0.length + flF.count false = gs2.length := by
    rw [hgs0_cnt, ← hflF_len]
    exact count_bool_sum flF
  have hn010_le_fl : n010 ≤ flF.count false :=
    filter_le_count_false gs2 flF hflF_len hP010_elim
  have hn10_le_n010 : n10 ≤ n010 := hfilter_mono gs2
  by_cases h3 : 3 ≤ n010
  · exact fromRestrict_14 (by omega)
  by_cases h1 : n010 = 1
  · have hn10_1 : n10 = 1 := by omega
    have hno0 : ∀ g ∈ gs2, (0 : ℕ) ∉ g.inputs := by
      intro g hm h0m
      obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hm
      have hcl := hgs2_clean j hj
      have hgd : gs2.getD j ⟨GateOp.or, []⟩ = g := by rw [List.getD_eq_getElem _ _ hj, hget]
      rw [hgd] at hcl
      have h10no : (10 : ℕ) ∉ g.inputs := by
        rcases hcl.1 with hop | hop | hop
        · intro h10m; exact (hcl.2.2.2.2 (Or.inl hop)).2 ⟨h0m, h10m⟩
        · intro h10m; exact (hcl.2.2.2.2 (Or.inr hop)).2 ⟨h0m, h10m⟩
        · exact (hcl.2.2.2.1 hop).2.2
      have hstrict := hfilter_strict gs2 g hm h0m h10no
      change n10 + 1 ≤ n010 at hstrict
      omega
    have h10_not : ∀ g ∈ gs2, (10 : ℕ) ∈ g.inputs → g.op ≠ GateOp.not := by
      intro g hm h10m hnot
      obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hm
      have hcl := hgs2_clean j hj
      have hgd : gs2.getD j ⟨GateOp.or, []⟩ = g := by rw [List.getD_eq_getElem _ _ hj, hget]
      rw [hgd] at hcl
      exact (hcl.2.2.2.1 hnot).2.2 h10m
    exact hD2_no_wit (hDeg1 D2 u2 v2 hD2_fan hD2_size hno0 hn10_1 h10_not hD2_uv1 hD2_uv2 hD2_pos)
  have hn010_2 : n010 = 2 := by omega
  by_cases hgood : (∀ g ∈ gs2, (0 : ℕ) ∈ g.inputs → g.op = GateOp.or) ∧
      (∀ g ∈ gs2, (10 : ℕ) ∈ g.inputs → g.op = GateOp.and)
  · have hex10 : ∃ g ∈ gs2, (10 : ℕ) ∈ g.inputs := by
      cases hfl : gs2.filter (fun g => g.inputs.contains (10 : ℕ)) with
      | nil =>
        have : n10 = 0 := by dsimp only [n10]; rw [hfl]; rfl
        omega
      | cons g _ =>
        have hmem : g ∈ gs2.filter (fun g => g.inputs.contains (10 : ℕ)) := by rw [hfl]; exact List.mem_cons_self
        obtain ⟨hmg, hcg⟩ := List.mem_filter.mp hmem
        exact ⟨g, hmg, List.contains_iff_mem.mp hcg⟩
    exact hD2_no_wit (hDeg2 D2 u2 v2 hD2_fan hD2_size hn010_2 hex10 (fun g hm => ⟨hgood.1 g hm, hgood.2 g hm⟩) hD2_uv1 hD2_uv2 hD2_pos)
  have hex_bad : ∃ j1 < gs2.length, P010 (gs2.getD j1 ⟨GateOp.or, []⟩) = true ∧
      ∃ c1 : Bool, stF.getD (11 + j1) (Sum.inl false) = Sum.inl c1 := by
    by_cases h0ok : ∀ g ∈ gs2, (0 : ℕ) ∈ g.inputs → g.op = GateOp.or
    · have h10bad : ∃ g ∈ gs2, (10 : ℕ) ∈ g.inputs ∧ g.op ≠ GateOp.and := by
        by_contra hall
        apply hgood
        refine ⟨h0ok, fun g hm h10m => ?_⟩
        by_contra hne
        exact hall ⟨g, hm, h10m, hne⟩
      obtain ⟨g1, hm1, h10m1, hne1⟩ := h10bad
      obtain ⟨j1, hj1, hget1⟩ := List.mem_iff_getElem.mp hm1
      have hgd1 : gs2.getD j1 ⟨GateOp.or, []⟩ = g1 := by rw [List.getD_eq_getElem _ _ hj1, hget1]
      have hcl1 := hgs2_clean j1 hj1
      rw [hgd1] at hcl1
      have hor1 : g1.op = GateOp.or := by
        rcases hcl1.1 with hop | hop | hop
        · exact (hne1 hop).elim
        · exact hop
        · exact ((hcl1.2.2.2.1 hop).2.2 h10m1).elim
      refine ⟨j1, hj1, by rw [hgd1]; exact (hP010_iff g1).mpr (Or.inr h10m1), true, ?_⟩
      exact hruleB_or_true j1 hj1 (by rw [hgd1]; exact hor1) ⟨10, by rw [hgd1]; exact h10m1, hstF_10⟩
    · have h0bad : ∃ g ∈ gs2, (0 : ℕ) ∈ g.inputs ∧ g.op ≠ GateOp.or := by
        by_contra hall
        apply h0ok
        intro g hm h0m
        by_contra hne
        exact hall ⟨g, hm, h0m, hne⟩
      obtain ⟨g1, hm1, h0m1, hne1⟩ := h0bad
      obtain ⟨j1, hj1, hget1⟩ := List.mem_iff_getElem.mp hm1
      have hgd1 : gs2.getD j1 ⟨GateOp.or, []⟩ = g1 := by rw [List.getD_eq_getElem _ _ hj1, hget1]
      have hcl1 := hgs2_clean j1 hj1
      rw [hgd1] at hcl1
      have hand1 : g1.op = GateOp.and := by
        rcases hcl1.1 with hop | hop | hop
        · exact hop
        · exact (hne1 hop).elim
        · exact ((hcl1.2.2.2.1 hop).2.1 h0m1).elim
      refine ⟨j1, hj1, by rw [hgd1]; exact (hP010_iff g1).mpr (Or.inl h0m1), false, ?_⟩
      exact hruleB_and_false j1 hj1 (by rw [hgd1]; exact hand1) ⟨0, by rw [hgd1]; exact h0m1, hstF_0⟩
  obtain ⟨j1, hj1, hPj1, c1, hc1⟩ := hex_bad
  rcases hgs2_reach j1 hj1 with hu_eq | hv_eq | ⟨j2, hj2, h12in⟩
  · exact fromRestrict_const (by omega) (Or.inl ⟨c1, by dsimp only [u0]; rw [← hu_eq]; exact hc1⟩)
  · exact fromRestrict_const (by omega) (Or.inr ⟨c1, by dsimp only [v0]; rw [← hv_eq]; exact hc1⟩)
  have hcl2 := hgs2_clean j2 hj2
  have hj12 : j1 < j2 := by have := hcl2.2.2.1 (11 + j1) h12in; omega
  have hfl2 : flF.getD j2 false = false := hruleA j2 hj2 ⟨11 + j1, h12in, c1, hc1⟩
  cases hPj2 : P010 (gs2.getD j2 ⟨GateOp.or, []⟩)
  · have h3fl := filter_succ_le_count_false gs2 flF j2 hflF_len hP010_elim hj2 hPj2 hfl2
    change n010 + 1 ≤ flF.count false at h3fl
    exact fromRestrict_14 (by omega)
  · have hbin2 : (gs2.getD j2 ⟨GateOp.or, []⟩).op = GateOp.and ∨ (gs2.getD j2 ⟨GateOp.or, []⟩).op = GateOp.or := by
      rcases hcl2.1 with hop | hop | hop
      · exact Or.inl hop
      · exact Or.inr hop
      · exfalso
        rcases (hP010_iff _).mp hPj2 with h0m | h10m
        · exact (hcl2.2.2.2.1 hop).2.1 h0m
        · exact (hcl2.2.2.2.1 hop).2.2 h10m
    have hboth2 : ∀ i ∈ (gs2.getD j2 ⟨GateOp.or, []⟩).inputs, ∃ b : Bool, stF.getD i (Sum.inl false) = Sum.inl b := by
      have hlen2 := (hcl2.2.2.2.2 hbin2).1
      cases hgi2 : (gs2.getD j2 ⟨GateOp.or, []⟩).inputs with
      | nil => rw [hgi2] at hlen2; simp at hlen2
      | cons a1 t1 =>
        cases t1 with
        | nil => rw [hgi2] at hlen2; simp at hlen2
        | cons a2 t2 =>
          cases t2 with
          | nil =>
            rw [hgi2] at h12in
            simp only [List.mem_cons, List.not_mem_nil, or_false] at h12in
            have h010_2 := (hP010_iff _).mp hPj2
            rw [hgi2] at h010_2
            simp only [List.mem_cons, List.not_mem_nil, or_false] at h010_2
            intro i hi
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases h12in with ha1 | ha2
            · rcases h010_2 with (h0a | h0b) | (h10a | h10b)
              · omega
              · rcases hi with rfl | rfl
                · exact ⟨c1, ha1 ▸ hc1⟩
                · exact ⟨false, h0b ▸ hstF_0⟩
              · omega
              · rcases hi with rfl | rfl
                · exact ⟨c1, ha1 ▸ hc1⟩
                · exact ⟨true, h10b ▸ hstF_10⟩
            · rcases h010_2 with (h0a | h0b) | (h10a | h10b)
              · rcases hi with rfl | rfl
                · exact ⟨false, h0a ▸ hstF_0⟩
                · exact ⟨c1, ha2 ▸ hc1⟩
              · omega
              · rcases hi with rfl | rfl
                · exact ⟨true, h10a ▸ hstF_10⟩
                · exact ⟨c1, ha2 ▸ hc1⟩
              · omega
          | cons _ _ => rw [hgi2] at hlen2; simp at hlen2
    obtain ⟨c2, hc2⟩ := hruleB_both_const j2 hj2 hbin2 hboth2
    rcases hgs2_reach j2 hj2 with hu_eq2 | hv_eq2 | ⟨j3, hj3, h23in⟩
    · exact fromRestrict_const (by omega) (Or.inl ⟨c2, by dsimp only [u0]; rw [← hu_eq2]; exact hc2⟩)
    · exact fromRestrict_const (by omega) (Or.inr ⟨c2, by dsimp only [v0]; rw [← hv_eq2]; exact hc2⟩)
    have hcl3 := hgs2_clean j3 hj3
    have hj23 : j2 < j3 := by have := hcl3.2.2.1 (11 + j2) h23in; omega
    have hfl3 : flF.getD j3 false = false := hruleA j3 hj3 ⟨11 + j2, h23in, c2, hc2⟩
    cases hPj3 : P010 (gs2.getD j3 ⟨GateOp.or, []⟩)
    · have h3fl := filter_succ_le_count_false gs2 flF j3 hflF_len hP010_elim hj3 hPj3 hfl3
      change n010 + 1 ≤ flF.count false at h3fl
      exact fromRestrict_14 (by omega)
    · have h3p := filter_ge_three gs2 j1 j2 j3 hj12 hj23 hj3 hPj1 hPj2 hPj3
      change 3 ≤ n010 at h3p
      omega
