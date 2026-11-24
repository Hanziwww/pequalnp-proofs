import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_5088_17
    (hP9Le15 : ∀ (D : Circuit), FanInTwo D → D.size ≤ 15 →
      ∃ (y : Fin 9 → Bool), D.eval (List.ofFn y) ≠
        (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 0 && y 5 || y 1 && y 6 ||
         y 2 && y 7 || y 3 && y 8 || y 4 && y 6 || y 6 && y 8 || y 8 && y 5 ||
         y 5 && y 7 || y 7 && y 4))
    (hDeg1Pos : ∀ (D : Circuit), FanInTwo D → D.size ≤ 18 →
      List.countP (fun (g : Gate) =>
        if g.op.eval [false] = true then g.inputs.head? == some 0 else g.inputs.contains 0) D.gates = 1 →
      ∃ (x : Fin 10 → Bool), D.eval (List.ofFn x) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
         x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5))
    (hDeg1Neg : ∀ (D : Circuit), FanInTwo D → D.size ≤ 18 →
      List.countP (fun (g : Gate) =>
        if g.op.eval [false] = true then g.inputs.head? == some 0 else g.inputs.contains 0) D.gates = 1 →
      ∃ (x : Fin 10 → Bool), D.eval (List.ofFn x) ≠
        (have z : Fin 10 → Bool := fun i => if i = 0 then !x 0 else x i
         z 0 && z 1 || z 1 && z 2 || z 2 && z 3 || z 3 && z 4 || z 4 && z 0 ||
         z 0 && z 5 || z 1 && z 6 || z 2 && z 7 || z 3 && z 8 || z 4 && z 9 ||
         z 5 && z 7 || z 7 && z 9 || z 9 && z 6 || z 6 && z 8 || z 8 && z 5))
    (hDeg2Exact18 : ∀ (C : Circuit), FanInTwo C → C.size = 18 →
      have e010 : Gate → Bool := fun g =>
        if g.op.eval [false] = true then g.inputs.head? == some 0 || g.inputs.head? == some 10
        else g.inputs.contains 0 || g.inputs.contains 10
      List.countP e010 C.gates = 2 →
      (∀ g ∈ C.gates, e010 g = true →
        (g.op = GateOp.and ∧ ∃ w, w ≠ 0 ∧ w ≠ 10 ∧ (g.inputs = [10, w] ∨ g.inputs = [w, 10])) ∨
        (g.op = GateOp.or ∧ ∃ w, w ≠ 0 ∧ w ≠ 10 ∧ (g.inputs = [0, w] ∨ g.inputs = [w, 0]))) →
      ∃ (x : Fin 10 → Bool), C.eval (List.ofFn x ++ [!x 0]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
         x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x1 →
      x1.size ≤ (18 : ℕ) →
      have x4 : ℕ := List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) =>
        if x4.op.eval [Bool.false] = Bool.true
        then x4.inputs.head? == Option.some (0 : ℕ) || x4.inputs.head? == Option.some (10 : ℕ)
        else x4.inputs.contains (0 : ℕ) || x4.inputs.contains (10 : ℕ)) x1.gates;
      (1 : ℕ) ≤ x4 →
      x4 ≤ (2 : ℕ) →
      ∃ (x7 : Fin (10 : ℕ) → Bool),
        x1.eval (List.ofFn x7 ++ [!x7 (0 : Fin (10 : ℕ))]) ≠
          (x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) ||
           x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) ||
           x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) ||
           x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) ||
           x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) ||
           x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) ||
           x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) ||
           x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) ||
           x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) ||
           x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) ||
           x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) ||
           x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) ||
           x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) ||
           x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) ||
           x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) := by
  intro C hfan hsz x4 hge1 hle2
  by_contra hno
  have hC : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!x 0]) =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
       x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
       x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) := by
    intro x
    by_contra hne
    exact hno ⟨x, hne⟩
  have eval_and : ∀ l, GateOp.and.eval l = l.all id := fun _ => rfl
  have eval_or : ∀ l, GateOp.or.eval l = l.any id := fun _ => rfl
  have eval_not : ∀ l, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  have eval_and_f : GateOp.and.eval [false] = false := rfl
  have eval_or_f : GateOp.or.eval [false] = false := rfl
  have eval_not_f : GateOp.not.eval [false] = true := rfl
  have eval_def : ∀ (D : Circuit) (xs : List Bool), D.eval xs = (D.wires xs).getD D.output false :=
    fun _ _ => rfl
  have wires_def : ∀ (D : Circuit) (xs : List Bool),
      D.wires xs = D.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs :=
    fun _ _ => rfl
  have size_def : ∀ (D : Circuit), D.size = D.gates.length := fun _ => rfl
  have getD_app_lt : ∀ {α : Type} (l1 l2 : List α) (i : ℕ) (d : α), i < l1.length →
      (l1 ++ l2).getD i d = l1.getD i d := by
    intro α l1 l2 i d hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getD_app_ge : ∀ {α : Type} (l1 l2 : List α) (i : ℕ) (d : α), l1.length ≤ i →
      (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
    intro α l1 l2 i d hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]
  let p10 : (Fin 10 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  let p9 : (Fin 9 → Bool) → Bool := fun y =>
    y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 0 && y 5 || y 1 && y 6 ||
    y 2 && y 7 || y 3 && y 8 || y 4 && y 6 || y 6 && y 8 || y 8 && y 5 ||
    y 5 && y 7 || y 7 && y 4
  let effReads : ℕ → Gate → Bool := fun w g =>
    if g.op.eval [false] = true then g.inputs.head? == some w else g.inputs.contains w
  let eff010 : Gate → Bool := fun g =>
    if g.op.eval [false] = true then g.inputs.head? == some 0 || g.inputs.head? == some 10
    else g.inputs.contains 0 || g.inputs.contains 10
  have heff010_eq : ∀ g, eff010 g = (effReads 0 g || effReads 10 g) := by
    intro g
    dsimp only [eff010, effReads]
    split_ifs <;> rfl
  have hfan_cases : ∀ (D : Circuit), FanInTwo D →
      ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro D hD g hg
    exact hD g hg
  have hfold_wires_prefix : ∀ (gs : List Gate) (W : List Bool),
      ∃ ext, gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W = W ++ ext ∧
        ext.length = gs.length := by
    intro gs
    induction gs with
    | nil => intro W; exact ⟨[], by simp, rfl⟩
    | cons g rest ih =>
      intro W
      obtain ⟨ext, hext, hlen⟩ := ih (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)])
      refine ⟨g.op.eval (g.inputs.map fun i => W.getD i false) :: ext, ?_, by simp [hlen]⟩
      simpa [List.foldl_cons, List.append_assoc] using hext
  have hgate_eval_congr : ∀ (g : Gate) (W1 W2 : List Bool),
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
      (∀ w, effReads w g = true → W1.getD w false = W2.getD w false) →
      g.op.eval (g.inputs.map fun i => W1.getD i false) =
      g.op.eval (g.inputs.map fun i => W2.getD i false) := by
    intro g W1 W2 hop hagree
    cases g with
    | mk op ins =>
      rcases hop with rfl | rfl | rfl
      · rw [eval_and, eval_and]
        have hmap : ins.map (fun i => W1.getD i false) = ins.map (fun i => W2.getD i false) := by
          apply List.map_congr_left
          intro w hw
          apply hagree w
          dsimp only [effReads]
          rw [eval_and_f]
          simp [hw]
        rw [hmap]
      · rw [eval_or, eval_or]
        have hmap : ins.map (fun i => W1.getD i false) = ins.map (fun i => W2.getD i false) := by
          apply List.map_congr_left
          intro w hw
          apply hagree w
          dsimp only [effReads]
          rw [eval_or_f]
          simp [hw]
        rw [hmap]
      · rw [eval_not, eval_not]
        cases ins with
        | nil => rfl
        | cons a rest =>
          simp only [List.map_cons, List.headD_cons]
          have ha : W1.getD a false = W2.getD a false := by
            apply hagree a
            dsimp only [effReads]
            rw [eval_not_f]
            simp
          rw [ha]
  have hp10_cons_false : ∀ y : Fin 9 → Bool, p10 (Fin.cons false y) = p9 y := by
    intro y
    dsimp only [p10, p9]
    have h0 : Fin.cons (α := fun _ => Bool) false y 0 = false := rfl
    have h1 : Fin.cons (α := fun _ => Bool) false y 1 = y 0 := rfl
    have h2 : Fin.cons (α := fun _ => Bool) false y 2 = y 1 := rfl
    have h3 : Fin.cons (α := fun _ => Bool) false y 3 = y 2 := rfl
    have h4 : Fin.cons (α := fun _ => Bool) false y 4 = y 3 := rfl
    have h5 : Fin.cons (α := fun _ => Bool) false y 5 = y 4 := rfl
    have h6 : Fin.cons (α := fun _ => Bool) false y 6 = y 5 := rfl
    have h7 : Fin.cons (α := fun _ => Bool) false y 7 = y 6 := rfl
    have h8 : Fin.cons (α := fun _ => Bool) false y 8 = y 7 := rfl
    have h9 : Fin.cons (α := fun _ => Bool) false y 9 = y 8 := rfl
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
    simp only [Bool.false_and, Bool.and_false, Bool.false_or, Bool.or_false]
  have hp10_not_const_false0 : ∀ b : Bool, ∃ y : Fin 9 → Bool, p10 (Fin.cons false y) ≠ b := by
    intro b
    cases b
    · refine ⟨fun i => decide (i = 0 ∨ i = 1), ?_⟩
      rw [hp10_cons_false]
      decide
    · refine ⟨fun _ => false, ?_⟩
      rw [hp10_cons_false]
      decide
  have hout_ne0 : ∀ (D : Circuit), (∀ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [!x 0]) = p10 x) →
      D.output ≠ 0 := by
    intro D hD h0
    let x0 : Fin 10 → Bool := fun i => decide (i = 0)
    have h1 := hD x0
    rw [eval_def, h0, wires_def] at h1
    obtain ⟨ext, hext, _⟩ := hfold_wires_prefix D.gates (List.ofFn x0 ++ [!x0 0])
    rw [hext, getD_app_lt _ _ _ _ (by simp)] at h1
    have hl : (List.ofFn x0 ++ [!x0 0]).getD 0 false = true := by
      rw [getD_app_lt _ _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD, x0]
    have hr : p10 x0 = false := by dsimp only [p10, x0]; decide
    rw [hl, hr] at h1
    exact Bool.noConfusion h1
  have hout_ne10 : ∀ (D : Circuit), (∀ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [!x 0]) = p10 x) →
      D.output ≠ 10 := by
    intro D hD h10
    let x0 : Fin 10 → Bool := fun _ => false
    have h1 := hD x0
    rw [eval_def, h10, wires_def] at h1
    obtain ⟨ext, hext, _⟩ := hfold_wires_prefix D.gates (List.ofFn x0 ++ [!x0 0])
    rw [hext, getD_app_lt _ _ _ _ (by simp)] at h1
    have hl : (List.ofFn x0 ++ [!x0 0]).getD 10 false = true := by
      rw [getD_app_ge _ _ _ _ (by simp)]
      simp [x0]
    have hr : p10 x0 = false := by dsimp only [p10, x0]; decide
    rw [hl, hr] at h1
    exact Bool.noConfusion h1
  have hDeg1 : ∀ (D : Circuit), FanInTwo D → D.size ≤ 18 → List.countP eff010 D.gates = 1 →
      (∀ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [!x 0]) = p10 x) → False := by
    intro D hDfan hDsz hDcnt hDcomp
    have hDne0 : D.output ≠ 0 := hout_ne0 D hDcomp
    have hDne10 : D.output ≠ 10 := hout_ne10 D hDcomp
    have hex_uniq : ∃ j0 < D.gates.length,
        eff010 (D.gates.getD j0 (Gate.mk GateOp.and [])) = true ∧
        ∀ j < D.gates.length, j ≠ j0 → eff010 (D.gates.getD j (Gate.mk GateOp.and [])) = false := by
      have haux : ∀ (gs : List Gate), List.countP eff010 gs = 1 →
          ∃ j0 < gs.length, eff010 (gs.getD j0 (Gate.mk GateOp.and [])) = true ∧
            ∀ j < gs.length, j ≠ j0 → eff010 (gs.getD j (Gate.mk GateOp.and [])) = false := by
        intro gs
        induction gs with
        | nil => intro h; simp at h
        | cons g rest ih =>
          intro h
          rw [List.countP_cons] at h
          cases hg : eff010 g
          · rw [hg] at h
            simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h
            obtain ⟨j0, hj0, htrue, hrest⟩ := ih h
            refine ⟨j0 + 1, by simp; omega, ?_, ?_⟩
            · simpa using htrue
            · intro j hj hne
              cases j with
              | zero => simpa using hg
              | succ j' => apply hrest j' (by simp at hj; omega) (by omega)
          · rw [hg] at h
            simp only [↓reduceIte] at h
            have hrest0 : List.countP eff010 rest = 0 := by omega
            have hall0 : ∀ x ∈ rest, eff010 x = false := by
              intro x hx
              have := List.countP_eq_zero.mp hrest0 x hx
              cases hx' : eff010 x
              · rfl
              · exact False.elim (this hx')
            refine ⟨0, by simp, by simpa using hg, ?_⟩
            intro j hj hne
            cases j with
            | zero => exact False.elim (hne rfl)
            | succ j' =>
              have hj' : j' < rest.length := by simp at hj; omega
              simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj'] using
                hall0 rest[j'] (List.getElem_mem hj')
      exact haux D.gates hDcnt
    obtain ⟨j0, hj0_lt, hj0_true, hj0_other⟩ := hex_uniq
    let g0 := D.gates.getD j0 (Gate.mk GateOp.and [])
    have hg0_mem : g0 ∈ D.gates := by
      dsimp only [g0]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj0_lt]
      exact List.getElem_mem hj0_lt
    have hnot_both : ¬ (effReads 0 g0 = true ∧ effReads 10 g0 = true) := by
      rintro ⟨h0, h10⟩
      obtain ⟨hop, hlen⟩ := hfan_cases D hDfan g0 hg0_mem
      have hg0_indep : ∀ (W1 W2 : List Bool),
          W1.getD 0 false = true → W1.getD 10 false = false →
          W2.getD 0 false = false → W2.getD 10 false = true →
          g0.op.eval (g0.inputs.map fun i => W1.getD i false) =
          g0.op.eval (g0.inputs.map fun i => W2.getD i false) := by
        intro W1 W2 h10' h11' h20' h21'
        rcases hop with hop_eq | hop_eq | hop_eq
        · rw [hop_eq, eval_and, eval_and]
          dsimp only [effReads] at h0 h10
          rw [hop_eq, eval_and_f] at h0 h10
          simp only [Bool.false_eq_true, ↓reduceIte, List.contains_eq_mem, decide_eq_true_eq] at h0 h10
          cases hin : g0.inputs with
          | nil => rw [hin] at h0; simp at h0
          | cons a rest =>
            cases rest with
            | nil => rw [hin] at h0 h10; simp at h0 h10; omega
            | cons b rest2 =>
              cases rest2 with
              | nil =>
                rw [hin] at h0 h10
                simp only [List.mem_cons, List.not_mem_nil, or_false] at h0 h10
                rcases h0 with rfl | rfl
                · rcases h10 with hbad | rfl
                  · omega
                  · simp only [List.map_cons, List.map_nil, h10', h11', h20', h21']; rfl
                · rcases h10 with rfl | hbad
                  · simp only [List.map_cons, List.map_nil, h10', h11', h20', h21']; rfl
                  · omega
              | cons c rest3 => rw [hin] at hlen; simp at hlen
        · rw [hop_eq, eval_or, eval_or]
          dsimp only [effReads] at h0 h10
          rw [hop_eq, eval_or_f] at h0 h10
          simp only [Bool.false_eq_true, ↓reduceIte, List.contains_eq_mem, decide_eq_true_eq] at h0 h10
          cases hin : g0.inputs with
          | nil => rw [hin] at h0; simp at h0
          | cons a rest =>
            cases rest with
            | nil => rw [hin] at h0 h10; simp at h0 h10; omega
            | cons b rest2 =>
              cases rest2 with
              | nil =>
                rw [hin] at h0 h10
                simp only [List.mem_cons, List.not_mem_nil, or_false] at h0 h10
                rcases h0 with rfl | rfl
                · rcases h10 with hbad | rfl
                  · omega
                  · simp only [List.map_cons, List.map_nil, h10', h11', h20', h21']; rfl
                · rcases h10 with rfl | hbad
                  · simp only [List.map_cons, List.map_nil, h10', h11', h20', h21']; rfl
                  · omega
              | cons c rest3 => rw [hin] at hlen; simp at hlen
        · dsimp only [effReads] at h0 h10
          rw [hop_eq, eval_not_f] at h0 h10
          simp only [↓reduceIte, beq_iff_eq] at h0 h10
          rw [h0] at h10
          cases h10
      let xB : Fin 10 → Bool := fun i => decide (i = 0 ∨ i = 1)
      let xA : Fin 10 → Bool := fun i => decide (i = 1)
      let W1_0 := List.ofFn xB ++ [!xB 0]
      let W2_0 := List.ofFn xA ++ [!xA 0]
      have hW_eq : ∀ (k : ℕ), k ≤ D.gates.length →
          ((D.gates.take k).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W1_0).length = 11 + k ∧
          ((D.gates.take k).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W2_0).length = 11 + k ∧
          ((D.gates.take k).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W1_0).getD 0 false = true ∧
          ((D.gates.take k).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W1_0).getD 10 false = false ∧
          ((D.gates.take k).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W2_0).getD 0 false = false ∧
          ((D.gates.take k).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W2_0).getD 10 false = true ∧
          ∀ w, w ≠ 0 → w ≠ 10 →
            ((D.gates.take k).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W1_0).getD w false =
            ((D.gates.take k).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W2_0).getD w false := by
        intro k
        induction k with
        | zero =>
          intro _
          simp only [List.take_zero, List.foldl_nil, Nat.add_zero]
          refine ⟨by simp [W1_0], by simp [W2_0],
            by dsimp only [W1_0]; rw [getD_app_lt _ _ _ _ (by simp)]; simp [List.getD_eq_getElem?_getD, xB],
            by dsimp only [W1_0]; rw [getD_app_ge _ _ _ _ (by simp)]; simp [xB],
            by dsimp only [W2_0]; rw [getD_app_lt _ _ _ _ (by simp)]; simp [List.getD_eq_getElem?_getD, xA],
            by dsimp only [W2_0]; rw [getD_app_ge _ _ _ _ (by simp)]; simp [xA], ?_⟩
          intro w hw0 hw10
          by_cases hlt : w < 10
          · dsimp only [W1_0, W2_0]
            rw [getD_app_lt _ _ _ _ (by simp; omega), getD_app_lt _ _ _ _ (by simp; omega)]
            simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some, xB, xA]
            have hne : (⟨w, hlt⟩ : Fin 10) ≠ 0 := by intro h; exact hw0 (congrArg Fin.val h)
            simp [hne]
          · have h1 : W1_0.length ≤ w := by simp [W1_0]; omega
            have h2 : W2_0.length ≤ w := by simp [W2_0]; omega
            rw [List.getD_eq_default _ _ h1, List.getD_eq_default _ _ h2]
        | succ k ih =>
          intro hk
          obtain ⟨hl1, hl2, h10', h11', h20', h21', hagr⟩ := ih (by omega)
          have htk : D.gates.take (k + 1) = D.gates.take k ++ [D.gates[k]] :=
            List.take_succ_eq_append_getElem (by omega)
          let gk := D.gates[k]
          let W1 := (D.gates.take k).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W1_0
          let W2 := (D.gates.take k).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W2_0
          have hval : gk.op.eval (gk.inputs.map fun i => W1.getD i false) =
              gk.op.eval (gk.inputs.map fun i => W2.getD i false) := by
            by_cases hkj : k = j0
            · subst hkj
              have hgk_eq : gk = g0 := by
                dsimp only [gk, g0]
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj0_lt]
                rfl
              rw [hgk_eq]
              exact hg0_indep W1 W2 h10' h11' h20' h21'
            · have hgk_mem : gk ∈ D.gates := List.getElem_mem (by omega)
              have hgk_f : eff010 gk = false := by
                have := hj0_other k (by omega) hkj
                simpa [gk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : k < D.gates.length)] using this
              rw [heff010_eq, Bool.or_eq_false_iff] at hgk_f
              apply hgate_eval_congr gk W1 W2 (hfan_cases D hDfan gk hgk_mem).1
              intro w hw
              apply hagr w
              · intro h0; subst h0; rw [hgk_f.1] at hw; cases hw
              · intro h10; subst h10; rw [hgk_f.2] at hw; cases hw
          simp only [htk, List.foldl_append, List.foldl_cons, List.foldl_nil]
          change (W1 ++ [gk.op.eval (gk.inputs.map fun i => W1.getD i false)]).length = 11 + (k + 1) ∧
            (W2 ++ [gk.op.eval (gk.inputs.map fun i => W2.getD i false)]).length = 11 + (k + 1) ∧
            (W1 ++ [gk.op.eval (gk.inputs.map fun i => W1.getD i false)]).getD 0 false = true ∧
            (W1 ++ [gk.op.eval (gk.inputs.map fun i => W1.getD i false)]).getD 10 false = false ∧
            (W2 ++ [gk.op.eval (gk.inputs.map fun i => W2.getD i false)]).getD 0 false = false ∧
            (W2 ++ [gk.op.eval (gk.inputs.map fun i => W2.getD i false)]).getD 10 false = true ∧
            ∀ w, w ≠ 0 → w ≠ 10 →
              (W1 ++ [gk.op.eval (gk.inputs.map fun i => W1.getD i false)]).getD w false =
              (W2 ++ [gk.op.eval (gk.inputs.map fun i => W2.getD i false)]).getD w false
          change W1.length = 11 + k at hl1
          change W2.length = 11 + k at hl2
          refine ⟨by rw [List.length_append, List.length_singleton, hl1]; omega,
            by rw [List.length_append, List.length_singleton, hl2]; omega,
            by rw [getD_app_lt _ _ _ _ (by omega)]; exact h10',
            by rw [getD_app_lt _ _ _ _ (by omega)]; exact h11',
            by rw [getD_app_lt _ _ _ _ (by omega)]; exact h20',
            by rw [getD_app_lt _ _ _ _ (by omega)]; exact h21', ?_⟩
          intro w hw0 hw10
          by_cases hlt : w < 11 + k
          · rw [getD_app_lt _ _ _ _ (by omega), getD_app_lt _ _ _ _ (by omega)]
            exact hagr w hw0 hw10
          · by_cases heq : w = 11 + k
            · subst heq
              rw [getD_app_ge _ _ _ _ (by omega), getD_app_ge _ _ _ _ (by omega)]
              simp only [hl1, hl2, Nat.sub_self, List.getD_cons_zero, hval]
            · rw [List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton, hl1]; omega),
                List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton, hl2]; omega)]
      obtain ⟨_, _, _, _, _, _, hagr_all⟩ := hW_eq D.gates.length (le_refl _)
      rw [List.take_length] at hagr_all
      have heval_eq : D.eval (List.ofFn xB ++ [!xB 0]) = D.eval (List.ofFn xA ++ [!xA 0]) := by
        rw [eval_def, eval_def, wires_def, wires_def]
        exact hagr_all D.output hDne0 hDne10
      rw [hDcomp xB, hDcomp xA] at heval_eq
      have hB : p10 xB = true := by dsimp only [p10, xB]; decide
      have hA : p10 xA = false := by dsimp only [p10, xA]; decide
      rw [hB, hA] at heval_eq
      exact Bool.noConfusion heval_eq
    let trimGate : (ℕ → ℕ) → Gate → Gate := fun f g =>
      Gate.mk g.op (if g.op.eval [false] = true then (g.inputs.take 1).map f else g.inputs.map f)
    have htrim_fan : ∀ (f : ℕ → ℕ), FanInTwo (Circuit.mk (D.gates.map (trimGate f)) (f D.output)) := by
      intro f g hg
      rw [List.mem_map] at hg
      obtain ⟨g', hg', rfl⟩ := hg
      obtain ⟨hop, hlen⟩ := hfan_cases D hDfan g' hg'
      dsimp only [trimGate]
      refine ⟨hop, ?_⟩
      split_ifs
      · simp
      · simp; exact hlen
    have htrim_eval_step : ∀ (f : ℕ → ℕ) (skip : ℕ) (g : Gate) (W1 W2 : List Bool),
        (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
        effReads skip g = false →
        (∀ w, w ≠ skip → W2.getD (f w) false = W1.getD w false) →
        (trimGate f g).op.eval ((trimGate f g).inputs.map fun i => W2.getD i false) =
        g.op.eval (g.inputs.map fun i => W1.getD i false) := by
      intro f skip g W1 W2 hop hskip hmap_eq
      cases g with
      | mk op ins =>
        dsimp only [trimGate]
        rcases hop with rfl | rfl | rfl
        · rw [eval_and_f]
          simp only [Bool.false_eq_true, ↓reduceIte, eval_and, List.map_map]
          have hlm : ins.map ((fun i => W2.getD i false) ∘ f) = ins.map (fun i => W1.getD i false) := by
            apply List.map_congr_left
            intro w hw
            apply hmap_eq w
            intro hweq; subst hweq
            dsimp only [effReads] at hskip
            rw [eval_and_f] at hskip
            simp [hw] at hskip
          rw [hlm]
        · rw [eval_or_f]
          simp only [Bool.false_eq_true, ↓reduceIte, eval_or, List.map_map]
          have hlm : ins.map ((fun i => W2.getD i false) ∘ f) = ins.map (fun i => W1.getD i false) := by
            apply List.map_congr_left
            intro w hw
            apply hmap_eq w
            intro hweq; subst hweq
            dsimp only [effReads] at hskip
            rw [eval_or_f] at hskip
            simp [hw] at hskip
          rw [hlm]
        · rw [eval_not_f]
          simp only [↓reduceIte, eval_not, List.map_map]
          cases ins with
          | nil => rfl
          | cons a rest =>
            simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
              List.headD_cons, Function.comp_apply]
            have hne : a ≠ skip := by
              intro hweq; subst hweq
              dsimp only [effReads] at hskip
              rw [eval_not_f] at hskip
              simp at hskip
            rw [hmap_eq a hne]
    have htrim_eff0 : ∀ (f : ℕ → ℕ) (skip target : ℕ) (g : Gate),
        (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
        effReads skip g = false →
        (∀ w, w ≠ skip → (f w = 0 ↔ w = target)) →
        (if (trimGate f g).op.eval [false] = true
          then (trimGate f g).inputs.head? == some 0
          else (trimGate f g).inputs.contains 0) = effReads target g := by
      intro f skip target g hop hskip hf0
      cases g with
      | mk op ins =>
        dsimp only [trimGate, effReads]
        rcases hop with rfl | rfl | rfl
        · rw [eval_and_f]
          simp only [Bool.false_eq_true, ↓reduceIte]
          apply Bool.eq_iff_iff.mpr
          simp only [List.contains_eq_mem, decide_eq_true_eq, List.mem_map]
          constructor
          · rintro ⟨w, hw, hfw⟩
            have hwne : w ≠ skip := by
              intro heq; subst heq
              dsimp only [effReads] at hskip
              rw [eval_and_f] at hskip
              simp [hw] at hskip
            rw [(hf0 w hwne).mp hfw] at hw
            exact hw
          · intro ht
            have htne : target ≠ skip := by
              intro heq; subst heq
              dsimp only [effReads] at hskip
              rw [eval_and_f] at hskip
              simp [ht] at hskip
            exact ⟨target, ht, (hf0 target htne).mpr rfl⟩
        · rw [eval_or_f]
          simp only [Bool.false_eq_true, ↓reduceIte]
          apply Bool.eq_iff_iff.mpr
          simp only [List.contains_eq_mem, decide_eq_true_eq, List.mem_map]
          constructor
          · rintro ⟨w, hw, hfw⟩
            have hwne : w ≠ skip := by
              intro heq; subst heq
              dsimp only [effReads] at hskip
              rw [eval_or_f] at hskip
              simp [hw] at hskip
            rw [(hf0 w hwne).mp hfw] at hw
            exact hw
          · intro ht
            have htne : target ≠ skip := by
              intro heq; subst heq
              dsimp only [effReads] at hskip
              rw [eval_or_f] at hskip
              simp [ht] at hskip
            exact ⟨target, ht, (hf0 target htne).mpr rfl⟩
        · rw [eval_not_f]
          simp only [↓reduceIte]
          cases ins with
          | nil => simp
          | cons a rest =>
            simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
              List.head?_cons]
            have hane : a ≠ skip := by
              intro heq; subst heq
              dsimp only [effReads] at hskip
              rw [eval_not_f] at hskip
              simp at hskip
            apply Bool.eq_iff_iff.mpr
            simp only [beq_iff_eq, Option.some.injEq]
            exact hf0 a hane
    have hg0_or : effReads 0 g0 = true ∨ effReads 10 g0 = true := by
      have := hj0_true
      rw [heff010_eq, Bool.or_eq_true] at this
      exact this
    rcases hg0_or with hg0_0 | hg0_10
    · have hg0_no10 : effReads 10 g0 = false := by
        cases h : effReads 10 g0
        · rfl
        · exact False.elim (hnot_both ⟨hg0_0, h⟩)
      have hall_no10 : ∀ g ∈ D.gates, effReads 10 g = false := by
        intro g hg
        rw [List.mem_iff_getElem] at hg
        obtain ⟨j, hj, rfl⟩ := hg
        by_cases hjj : j = j0
        · subst hjj
          simpa [g0, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using hg0_no10
        · have hf := hj0_other j hj hjj
          rw [heff010_eq, Bool.or_eq_false_iff] at hf
          simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using hf.2
      let fPos : ℕ → ℕ := fun w => if w < 10 then w else w - 1
      let D' : Circuit := Circuit.mk (D.gates.map (trimGate fPos)) (fPos D.output)
      have hD'fan : FanInTwo D' := htrim_fan fPos
      have hD'sz : D'.size ≤ 18 := by rw [size_def]; simp [D']; exact hDsz
      have hD'cnt : List.countP (fun (g : Gate) =>
          if g.op.eval [false] = true then g.inputs.head? == some 0 else g.inputs.contains 0) D'.gates = 1 := by
        dsimp only [D']
        rw [List.countP_map]
        have hcongr : ∀ g ∈ D.gates,
            ((fun g : Gate => if g.op.eval [false] = true then g.inputs.head? == some 0 else g.inputs.contains 0) ∘
              trimGate fPos) g = eff010 g := by
          intro g hg
          dsimp only [Function.comp_apply]
          have h10 := hall_no10 g hg
          rw [htrim_eff0 fPos 10 0 g (hfan_cases D hDfan g hg).1 h10]
          · rw [heff010_eq, h10, Bool.or_false]
          · intro w _
            dsimp only [fPos]
            split_ifs <;> omega
        rw [List.countP_congr (fun g hg => by rw [hcongr g hg])]
        exact hDcnt
      obtain ⟨x, hx⟩ := hDeg1Pos D' hD'fan hD'sz hD'cnt
      have hD'eval : D'.eval (List.ofFn x) = D.eval (List.ofFn x ++ [!x 0]) := by
        rw [eval_def, eval_def, wires_def, wires_def]
        have hfold : ∀ (gs : List Gate), (∀ g ∈ gs, g ∈ D.gates) →
            ∀ (W1 W2 : List Bool), W1.length = W2.length + 1 → 10 ≤ W2.length →
            (∀ w, w ≠ 10 → W2.getD (fPos w) false = W1.getD w false) →
            ∀ w, w ≠ 10 →
              ((gs.map (trimGate fPos)).foldl
                (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W2).getD (fPos w) false =
              (gs.foldl
                (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W1).getD w false := by
          intro gs
          induction gs with
          | nil => intro _ W1 W2 _ _ hagr w hw; exact hagr w hw
          | cons g rest ih =>
            intro hmem W1 W2 hlen h10le hagr
            have hgD : g ∈ D.gates := hmem g (by simp)
            have hstep : (trimGate fPos g).op.eval ((trimGate fPos g).inputs.map fun i => W2.getD i false) =
                g.op.eval (g.inputs.map fun i => W1.getD i false) :=
              htrim_eval_step fPos 10 g W1 W2 (hfan_cases D hDfan g hgD).1 (hall_no10 g hgD) hagr
            simp only [List.map_cons, List.foldl_cons]
            apply ih (fun g' hg' => hmem g' (by simp [hg']))
            · simp [hlen]
            · simp; omega
            · intro w hw10
              by_cases hlt : w < W1.length
              · have hlt2 : fPos w < W2.length := by dsimp only [fPos]; split_ifs <;> omega
                rw [getD_app_lt _ _ _ _ hlt2, getD_app_lt _ _ _ _ hlt]
                exact hagr w hw10
              · by_cases heq : w = W1.length
                · subst heq
                  have hfw : fPos W1.length = W2.length := by dsimp only [fPos]; split_ifs <;> omega
                  rw [hfw, getD_app_ge _ _ _ _ (le_refl _), getD_app_ge _ _ _ _ (le_refl _)]
                  simp only [Nat.sub_self, List.getD_cons_zero]
                  exact hstep
                · have hge2 : (W2 ++ [(trimGate fPos g).op.eval ((trimGate fPos g).inputs.map fun i => W2.getD i false)]).length ≤ fPos w := by
                    dsimp only [fPos]; simp; split_ifs <;> omega
                  have hge1 : (W1 ++ [g.op.eval (g.inputs.map fun i => W1.getD i false)]).length ≤ w := by
                    simp; omega
                  rw [List.getD_eq_default _ _ hge2, List.getD_eq_default _ _ hge1]
        apply hfold D.gates (fun _ hg => hg) (List.ofFn x ++ [!x 0]) (List.ofFn x)
          (by simp) (by simp) _ D.output hDne10
        intro w hw10
        by_cases hlt : w < 10
        · have hfw : fPos w = w := by dsimp only [fPos]; simp [hlt]
          rw [hfw, getD_app_lt _ _ _ _ (by simp; exact hlt)]
        · have hge2 : (List.ofFn x).length ≤ fPos w := by dsimp only [fPos]; simp; split_ifs; omega
          have hge1 : (List.ofFn x ++ [!x 0]).length ≤ w := by simp; omega
          rw [List.getD_eq_default _ _ hge2, List.getD_eq_default _ _ hge1]
      exact hx (hD'eval.trans (hDcomp x))
    · have hg0_no0 : effReads 0 g0 = false := by
        cases h : effReads 0 g0
        · rfl
        · exact False.elim (hnot_both ⟨h, hg0_10⟩)
      have hall_no0 : ∀ g ∈ D.gates, effReads 0 g = false := by
        intro g hg
        rw [List.mem_iff_getElem] at hg
        obtain ⟨j, hj, rfl⟩ := hg
        by_cases hjj : j = j0
        · subst hjj
          simpa [g0, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using hg0_no0
        · have hf := hj0_other j hj hjj
          rw [heff010_eq, Bool.or_eq_false_iff] at hf
          simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using hf.1
      let fNeg : ℕ → ℕ := fun w => if w = 10 then 0 else if w < 10 then w else w - 1
      let D' : Circuit := Circuit.mk (D.gates.map (trimGate fNeg)) (fNeg D.output)
      have hD'fan : FanInTwo D' := htrim_fan fNeg
      have hD'sz : D'.size ≤ 18 := by rw [size_def]; simp [D']; exact hDsz
      have hD'cnt : List.countP (fun (g : Gate) =>
          if g.op.eval [false] = true then g.inputs.head? == some 0 else g.inputs.contains 0) D'.gates = 1 := by
        dsimp only [D']
        rw [List.countP_map]
        have hcongr : ∀ g ∈ D.gates,
            ((fun g : Gate => if g.op.eval [false] = true then g.inputs.head? == some 0 else g.inputs.contains 0) ∘
              trimGate fNeg) g = eff010 g := by
          intro g hg
          dsimp only [Function.comp_apply]
          have h0 := hall_no0 g hg
          rw [htrim_eff0 fNeg 0 10 g (hfan_cases D hDfan g hg).1 h0]
          · rw [heff010_eq, h0, Bool.false_or]
          · intro w hw0
            dsimp only [fNeg]
            split_ifs <;> omega
        rw [List.countP_congr (fun g hg => by rw [hcongr g hg])]
        exact hDcnt
      obtain ⟨x, hx⟩ := hDeg1Neg D' hD'fan hD'sz hD'cnt
      let z : Fin 10 → Bool := fun i => if i = 0 then !x 0 else x i
      have hD'eval : D'.eval (List.ofFn x) = D.eval (List.ofFn z ++ [!z 0]) := by
        rw [eval_def, eval_def, wires_def, wires_def]
        have hfold : ∀ (gs : List Gate), (∀ g ∈ gs, g ∈ D.gates) →
            ∀ (W1 W2 : List Bool), W1.length = W2.length + 1 → 10 ≤ W2.length →
            (∀ w, w ≠ 0 → W2.getD (fNeg w) false = W1.getD w false) →
            ∀ w, w ≠ 0 →
              ((gs.map (trimGate fNeg)).foldl
                (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W2).getD (fNeg w) false =
              (gs.foldl
                (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W1).getD w false := by
          intro gs
          induction gs with
          | nil => intro _ W1 W2 _ _ hagr w hw; exact hagr w hw
          | cons g rest ih =>
            intro hmem W1 W2 hlen h10le hagr
            have hgD : g ∈ D.gates := hmem g (by simp)
            have hstep : (trimGate fNeg g).op.eval ((trimGate fNeg g).inputs.map fun i => W2.getD i false) =
                g.op.eval (g.inputs.map fun i => W1.getD i false) :=
              htrim_eval_step fNeg 0 g W1 W2 (hfan_cases D hDfan g hgD).1 (hall_no0 g hgD) hagr
            simp only [List.map_cons, List.foldl_cons]
            apply ih (fun g' hg' => hmem g' (by simp [hg']))
            · simp [hlen]
            · simp; omega
            · intro w hw0
              by_cases hlt : w < W1.length
              · have hlt2 : fNeg w < W2.length := by dsimp only [fNeg]; split_ifs <;> omega
                rw [getD_app_lt _ _ _ _ hlt2, getD_app_lt _ _ _ _ hlt]
                exact hagr w hw0
              · by_cases heq : w = W1.length
                · subst heq
                  have hfw : fNeg W1.length = W2.length := by dsimp only [fNeg]; split_ifs <;> omega
                  rw [hfw, getD_app_ge _ _ _ _ (le_refl _), getD_app_ge _ _ _ _ (le_refl _)]
                  simp only [Nat.sub_self, List.getD_cons_zero]
                  exact hstep
                · have hge2 : (W2 ++ [(trimGate fNeg g).op.eval ((trimGate fNeg g).inputs.map fun i => W2.getD i false)]).length ≤ fNeg w := by
                    dsimp only [fNeg]; simp; split_ifs <;> omega
                  have hge1 : (W1 ++ [g.op.eval (g.inputs.map fun i => W1.getD i false)]).length ≤ w := by
                    simp; omega
                  rw [List.getD_eq_default _ _ hge2, List.getD_eq_default _ _ hge1]
        apply hfold D.gates (fun _ hg => hg) (List.ofFn z ++ [!z 0]) (List.ofFn x)
          (by simp) (by simp) _ D.output hDne0
        intro w hw0
        by_cases h10 : w = 10
        · subst h10
          have hfw : fNeg 10 = 0 := rfl
          rw [hfw, getD_app_ge _ _ _ _ (by simp)]
          simp [z, List.getD_eq_getElem?_getD]
        · by_cases hlt : w < 10
          · have hfw : fNeg w = w := by dsimp only [fNeg]; simp [h10, hlt]
            rw [hfw, getD_app_lt _ _ _ _ (by simp; exact hlt)]
            have hne : (⟨w, hlt⟩ : Fin 10) ≠ 0 := by intro h; exact hw0 (congrArg Fin.val h)
            simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some, z, hne, ↓reduceIte]
          · have hge2 : (List.ofFn x).length ≤ fNeg w := by dsimp only [fNeg]; simp; split_ifs; omega
            have hge1 : (List.ofFn z ++ [!z 0]).length ≤ w := by simp; omega
            rw [List.getD_eq_default _ _ hge2, List.getD_eq_default _ _ hge1]
      exact hx (hD'eval.trans (hDcomp z))
  by_cases hx1 : x4 = 1
  · exact hDeg1 C hfan hsz hx1 hC
  have hx2 : x4 = 2 := by omega
  let env0 : List (Sum Bool ℕ) :=
    [Sum.inl false,
     Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inr 4,
     Sum.inr 5, Sum.inr 6, Sum.inr 7, Sum.inr 8,
     Sum.inl true]
  let valOf : List Bool → Sum Bool ℕ → Bool := fun W => Sum.elim id (fun u => W.getD u false)
  let stepGate : List (Sum Bool ℕ) → ℕ → Gate → Sum Bool ℕ × Option Gate := fun env outLen g =>
    let look : ℕ → Sum Bool ℕ := fun w => env.getD w (Sum.inl false)
    GateOp.rec
      (List.casesOn g.inputs
        (Sum.inl true, none)
        (fun a rest =>
          List.casesOn rest
            (look a, none)
            (fun b _ =>
              Sum.elim
                (fun ba => if ba = true then (look b, none) else (Sum.inl false, none))
                (fun u =>
                  Sum.elim
                    (fun bb => if bb = true then (Sum.inr u, none) else (Sum.inl false, none))
                    (fun v => (Sum.inr outLen, some (Gate.mk GateOp.and [u, v])))
                    (look b))
                (look a))))
      (List.casesOn g.inputs
        (Sum.inl false, none)
        (fun a rest =>
          List.casesOn rest
            (look a, none)
            (fun b _ =>
              Sum.elim
                (fun ba => if ba = true then (Sum.inl true, none) else (look b, none))
                (fun u =>
                  Sum.elim
                    (fun bb => if bb = true then (Sum.inl true, none) else (Sum.inr u, none))
                    (fun v => (Sum.inr outLen, some (Gate.mk GateOp.or [u, v])))
                    (look b))
                (look a))))
      (List.casesOn g.inputs
        (Sum.inl true, none)
        (fun a _ =>
          Sum.elim
            (fun ba => (Sum.inl (!ba), none))
            (fun u => (Sum.inr outLen, some (Gate.mk GateOp.not [u])))
            (look a)))
      (fun _ => (Sum.inl false, none))
      (Sum.inl false, none)
      g.op
  let stepOne : List (Sum Bool ℕ) × List Gate → Gate → List (Sum Bool ℕ) × List Gate := fun st g =>
    let r := stepGate st.1 (9 + st.2.length) g
    (st.1 ++ [r.1], Option.rec st.2 (fun g' => st.2 ++ [g']) r.2)
  have hstep_fan : ∀ env outLen g g', (stepGate env outLen g).2 = some g' →
      (g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not) ∧ g'.inputs.length ≤ 2 := by
    intro env outLen g g' h
    cases g with
    | mk op ins =>
      cases op with
      | and =>
        cases ins with
        | nil => cases h
        | cons a rest =>
          cases rest with
          | nil => cases h
          | cons b rest2 =>
            dsimp only [stepGate] at h
            cases ha : env.getD a (Sum.inl false) with
            | inl ba =>
              rw [ha] at h; cases ba <;> simp at h
            | inr u =>
              rw [ha] at h
              cases hb : env.getD b (Sum.inl false) with
              | inl bb =>
                rw [hb] at h; cases bb <;> simp at h
              | inr v =>
                rw [hb] at h
                simp only [Sum.elim_inr, Option.some.injEq] at h
                rw [← h]; exact ⟨Or.inl rfl, by simp⟩
      | or =>
        cases ins with
        | nil => cases h
        | cons a rest =>
          cases rest with
          | nil => cases h
          | cons b rest2 =>
            dsimp only [stepGate] at h
            cases ha : env.getD a (Sum.inl false) with
            | inl ba =>
              rw [ha] at h; cases ba <;> simp at h
            | inr u =>
              rw [ha] at h
              cases hb : env.getD b (Sum.inl false) with
              | inl bb =>
                rw [hb] at h; cases bb <;> simp at h
              | inr v =>
                rw [hb] at h
                simp only [Sum.elim_inr, Option.some.injEq] at h
                rw [← h]; exact ⟨Or.inr (Or.inl rfl), by simp⟩
      | not =>
        cases ins with
        | nil => cases h
        | cons a rest =>
          dsimp only [stepGate] at h
          cases ha : env.getD a (Sum.inl false) with
          | inl ba => rw [ha] at h; simp at h
          | inr u =>
            rw [ha] at h
            simp only [Sum.elim_inr, Option.some.injEq] at h
            rw [← h]; exact ⟨Or.inr (Or.inr rfl), by simp⟩
      | mod m => cases h
      | maj => cases h
  have hstep_const_none : ∀ env outLen g w b,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
      g.inputs.length ≤ 2 →
      effReads w g = true →
      env.getD w (Sum.inl false) = Sum.inl b →
      (stepGate env outLen g).2 = none := by
    intro env outLen g w b hop hlen hreads hlook
    cases g with
    | mk op ins =>
      rcases hop with rfl | rfl | rfl
      · dsimp only [effReads] at hreads
        rw [eval_and_f] at hreads
        simp only [Bool.false_eq_true, ↓reduceIte, List.contains_eq_mem, decide_eq_true_eq] at hreads
        cases ins with
        | nil => rfl
        | cons a rest =>
          cases rest with
          | nil => rfl
          | cons c rest2 =>
            cases rest2 with
            | nil =>
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hreads
              dsimp only [stepGate]
              rcases hreads with rfl | rfl
              · rw [hlook]; cases b <;> rfl
              · cases ha : env.getD a (Sum.inl false) with
                | inl ba => cases ba <;> rfl
                | inr u => rw [hlook]; cases b <;> rfl
            | cons d rest3 => simp at hlen
      · dsimp only [effReads] at hreads
        rw [eval_or_f] at hreads
        simp only [Bool.false_eq_true, ↓reduceIte, List.contains_eq_mem, decide_eq_true_eq] at hreads
        cases ins with
        | nil => rfl
        | cons a rest =>
          cases rest with
          | nil => rfl
          | cons c rest2 =>
            cases rest2 with
            | nil =>
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hreads
              dsimp only [stepGate]
              rcases hreads with rfl | rfl
              · rw [hlook]; cases b <;> rfl
              · cases ha : env.getD a (Sum.inl false) with
                | inl ba => cases ba <;> rfl
                | inr u => rw [hlook]; cases b <;> rfl
            | cons d rest3 => simp at hlen
      · dsimp only [effReads] at hreads
        rw [eval_not_f] at hreads
        simp only [↓reduceIte, beq_iff_eq] at hreads
        cases ins with
        | nil => rfl
        | cons a rest =>
          simp only [List.head?_cons, Option.some.injEq] at hreads
          subst hreads
          dsimp only [stepGate]
          rw [hlook]; rfl
  have hstep_eff010_none : ∀ env outLen g,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
      g.inputs.length ≤ 2 →
      env.getD 0 (Sum.inl false) = Sum.inl false →
      env.getD 10 (Sum.inl false) = Sum.inl true →
      eff010 g = true →
      (stepGate env outLen g).2 = none := by
    intro env outLen g hop hlen h0 h10 heff
    rw [heff010_eq, Bool.or_eq_true] at heff
    rcases heff with h | h
    · exact hstep_const_none env outLen g 0 false hop hlen h h0
    · exact hstep_const_none env outLen g 10 true hop hlen h h10
  have hstep_sem : ∀ (env : List (Sum Bool ℕ)) (W_in W_out : List Bool) (g : Gate),
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
      g.inputs.length ≤ 2 →
      env.length = W_in.length →
      (∀ s ∈ env, Sum.elim (fun _ => True) (fun u => u < W_out.length) s) →
      (∀ w, W_in.getD w false = valOf W_out (env.getD w (Sum.inl false))) →
      let r := stepGate env W_out.length g
      let W_in' := W_in ++ [g.op.eval (g.inputs.map fun i => W_in.getD i false)]
      let W_out' := Option.rec W_out (fun g' => W_out ++ [g'.op.eval (g'.inputs.map fun i => W_out.getD i false)]) r.2
      let env' := env ++ [r.1]
      env'.length = W_in'.length ∧
      (∀ s ∈ env', Sum.elim (fun _ => True) (fun u => u < W_out'.length) s) ∧
      (∀ w, W_in'.getD w false = valOf W_out' (env'.getD w (Sum.inl false))) := by
    intro env W_in W_out g hop hlen hlen_eq hlt_env hagr
    have hlook_lt : ∀ w, Sum.elim (fun _ => True) (fun u => u < W_out.length) (env.getD w (Sum.inl false)) := by
      intro w
      by_cases hw : w < env.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw]
        exact hlt_env env[w] (List.getElem_mem hw)
      · rw [List.getD_eq_default _ _ (by omega)]
        trivial
    have hcore :
        let r := stepGate env W_out.length g
        let W_out' := Option.rec W_out (fun g' => W_out ++ [g'.op.eval (g'.inputs.map fun i => W_out.getD i false)]) r.2
        W_out.length ≤ W_out'.length ∧
        (∀ u < W_out.length, W_out'.getD u false = W_out.getD u false) ∧
        Sum.elim (fun _ => True) (fun u => u < W_out'.length) r.1 ∧
        g.op.eval (g.inputs.map fun i => W_in.getD i false) = valOf W_out' r.1 := by
      cases g with
      | mk op ins =>
        rcases hop with rfl | rfl | rfl
        · rw [eval_and]
          cases ins with
          | nil => exact ⟨le_refl _, fun _ _ => rfl, trivial, rfl⟩
          | cons a rest =>
            cases rest with
            | nil =>
              dsimp only [stepGate]
              refine ⟨le_refl _, fun _ _ => rfl, hlook_lt a, ?_⟩
              simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
              exact hagr a
            | cons b rest2 =>
              cases rest2 with
              | nil =>
                have ha := hagr a
                have hb := hagr b
                dsimp only [stepGate]
                cases hla : env.getD a (Sum.inl false) with
                | inl ba =>
                  dsimp only [Sum.elim_inl]
                  cases ba
                  · refine ⟨le_refl _, fun _ _ => rfl, trivial, ?_⟩
                    simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, ha, hla, valOf,
                      Sum.elim_inl, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
                  · refine ⟨le_refl _, fun _ _ => rfl, hlook_lt b, ?_⟩
                    simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, ha, hb, hla, valOf,
                      Sum.elim_inl, Bool.true_and, Bool.and_true, ↓reduceIte]
                | inr u =>
                  dsimp only [Sum.elim_inr]
                  cases hlb : env.getD b (Sum.inl false) with
                  | inl bb =>
                    dsimp only [Sum.elim_inl]
                    cases bb
                    · refine ⟨le_refl _, fun _ _ => rfl, trivial, ?_⟩
                      simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, hb, hlb, valOf,
                        Sum.elim_inl, Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
                    · have hu_lt : u < W_out.length := by have h := hlook_lt a; rw [hla] at h; exact h
                      refine ⟨le_refl _, fun _ _ => rfl, hu_lt, ?_⟩
                      simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, ha, hb, hla, hlb,
                        valOf, Sum.elim_inl, Sum.elim_inr, Bool.and_true, ↓reduceIte]
                  | inr v =>
                    dsimp only [Sum.elim_inr]
                    refine ⟨by simp, fun k hk => getD_app_lt _ _ _ _ hk, by simp, ?_⟩
                    dsimp only [valOf]
                    rw [Sum.elim_inr, getD_app_ge _ _ _ _ (le_refl _)]
                    simp only [Nat.sub_self, List.getD_cons_zero, eval_and, List.map_cons, List.map_nil,
                      List.all_cons, List.all_nil, id_eq, ha, hb, hla, hlb, valOf, Sum.elim_inr]
              | cons c rest3 => simp at hlen
        · rw [eval_or]
          cases ins with
          | nil => exact ⟨le_refl _, fun _ _ => rfl, trivial, rfl⟩
          | cons a rest =>
            cases rest with
            | nil =>
              dsimp only [stepGate]
              refine ⟨le_refl _, fun _ _ => rfl, hlook_lt a, ?_⟩
              simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
              exact hagr a
            | cons b rest2 =>
              cases rest2 with
              | nil =>
                have ha := hagr a
                have hb := hagr b
                dsimp only [stepGate]
                cases hla : env.getD a (Sum.inl false) with
                | inl ba =>
                  dsimp only [Sum.elim_inl]
                  cases ba
                  · refine ⟨le_refl _, fun _ _ => rfl, hlook_lt b, ?_⟩
                    simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, ha, hb, hla, valOf,
                      Sum.elim_inl, Bool.false_or, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
                  · refine ⟨le_refl _, fun _ _ => rfl, trivial, ?_⟩
                    simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, ha, hla, valOf,
                      Sum.elim_inl, Bool.true_or, ↓reduceIte]
                | inr u =>
                  dsimp only [Sum.elim_inr]
                  cases hlb : env.getD b (Sum.inl false) with
                  | inl bb =>
                    dsimp only [Sum.elim_inl]
                    cases bb
                    · have hu_lt : u < W_out.length := by have h := hlook_lt a; rw [hla] at h; exact h
                      refine ⟨le_refl _, fun _ _ => rfl, hu_lt, ?_⟩
                      simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, ha, hb, hla, hlb,
                        valOf, Sum.elim_inl, Sum.elim_inr, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
                    · refine ⟨le_refl _, fun _ _ => rfl, trivial, ?_⟩
                      simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, hb, hlb, valOf,
                        Sum.elim_inl, Bool.true_or, Bool.or_true, ↓reduceIte]
                  | inr v =>
                    dsimp only [Sum.elim_inr]
                    refine ⟨by simp, fun k hk => getD_app_lt _ _ _ _ hk, by simp, ?_⟩
                    dsimp only [valOf]
                    rw [Sum.elim_inr, getD_app_ge _ _ _ _ (le_refl _)]
                    simp only [Nat.sub_self, List.getD_cons_zero, eval_or, List.map_cons, List.map_nil,
                      List.any_cons, List.any_nil, id_eq, ha, hb, hla, hlb, valOf, Sum.elim_inr]
              | cons c rest3 => simp at hlen
        · rw [eval_not]
          cases ins with
          | nil => exact ⟨le_refl _, fun _ _ => rfl, trivial, rfl⟩
          | cons a rest =>
            have ha := hagr a
            dsimp only [stepGate]
            cases hla : env.getD a (Sum.inl false) with
            | inl ba =>
              dsimp only [Sum.elim_inl]
              refine ⟨le_refl _, fun _ _ => rfl, trivial, ?_⟩
              simp only [List.map_cons, List.headD_cons, ha, hla, valOf, Sum.elim_inl, id_eq]
            | inr u =>
              dsimp only [Sum.elim_inr]
              refine ⟨by simp, fun k hk => getD_app_lt _ _ _ _ hk, by simp, ?_⟩
              dsimp only [valOf]
              rw [Sum.elim_inr, getD_app_ge _ _ _ _ (le_refl _)]
              simp only [Nat.sub_self, List.getD_cons_zero, eval_not, List.map_cons, List.map_nil,
                List.headD_cons, ha, hla, valOf, Sum.elim_inr]
    obtain ⟨hlen_out, hpres_out, hr_lt, hval_eq⟩ := hcore
    refine ⟨by simp [hlen_eq], ?_, ?_⟩
    · intro s hs
      rw [List.mem_append] at hs
      rcases hs with hs | hs
      · have := hlt_env s hs
        cases s with
        | inl _ => trivial
        | inr u => exact lt_of_lt_of_le this hlen_out
      · simp only [List.mem_singleton] at hs
        subst hs
        exact hr_lt
    · intro w
      by_cases hw : w < env.length
      · rw [getD_app_lt _ _ _ _ (by omega), getD_app_lt _ _ _ _ hw, hagr w]
        have hltw := hlook_lt w
        cases hew : env.getD w (Sum.inl false) with
        | inl _ => rfl
        | inr u =>
          rw [hew] at hltw
          exact (hpres_out u hltw).symm
      · by_cases heq : w = env.length
        · subst heq
          rw [getD_app_ge _ _ _ _ (by omega), getD_app_ge _ _ _ _ (le_refl _)]
          simp only [hlen_eq, Nat.sub_self, List.getD_cons_zero]
          exact hval_eq
        · rw [List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp; omega)]
          rfl
  have hfold_prefix : ∀ (gs : List Gate) (env : List (Sum Bool ℕ)) (em : List Gate),
      ∃ ext, (gs.foldl stepOne (env, em)).1 = env ++ ext ∧ ext.length = gs.length := by
    intro gs
    induction gs with
    | nil => intro env em; exact ⟨[], by simp, rfl⟩
    | cons g rest ih =>
      intro env em
      obtain ⟨ext, hext, hlen⟩ := ih (stepOne (env, em) g).1 (stepOne (env, em) g).2
      refine ⟨(stepGate env (9 + em.length) g).1 :: ext, ?_, by simp [hlen]⟩
      simpa [List.foldl_cons, stepOne, List.append_assoc] using hext
  have hfold_bound : ∀ (gs : List Gate) (env : List (Sum Bool ℕ)) (em : List Gate),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
      11 ≤ env.length →
      env.getD 0 (Sum.inl false) = Sum.inl false →
      env.getD 10 (Sum.inl false) = Sum.inl true →
      (gs.foldl stepOne (env, em)).2.length + List.countP eff010 gs ≤ em.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro env em _ _ _ _; simp
    | cons g rest ih =>
      intro env em hgs hlen11 h0 h10
      obtain ⟨hop, hglen⟩ := hgs g (by simp)
      have hlen' : 11 ≤ (stepOne (env, em) g).1.length := by dsimp only [stepOne]; simp; omega
      have h0' : (stepOne (env, em) g).1.getD 0 (Sum.inl false) = Sum.inl false := by
        dsimp only [stepOne]; rw [getD_app_lt _ _ _ _ (by omega)]; exact h0
      have h10' : (stepOne (env, em) g).1.getD 10 (Sum.inl false) = Sum.inl true := by
        dsimp only [stepOne]; rw [getD_app_lt _ _ _ _ (by omega)]; exact h10
      have hih := ih (stepOne (env, em) g).1 (stepOne (env, em) g).2
        (fun g' hg' => hgs g' (by simp [hg'])) hlen' h0' h10'
      have hstep_len : (stepOne (env, em) g).2.length + (if eff010 g = true then 1 else 0) ≤ em.length + 1 := by
        dsimp only [stepOne]
        by_cases he : eff010 g = true
        · rw [hstep_eff010_none env (9 + em.length) g hop hglen h0 h10 he]
          simp [he]
        · simp only [he]
          cases (stepGate env (9 + em.length) g).2 <;> simp
      rw [List.foldl_cons, List.countP_cons]
      simp only [List.length_cons]
      simp only [Prod.mk.eta] at hih
      cases he : eff010 g
      · simp only [he, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hstep_len ⊢; omega
      · simp only [he, ↓reduceIte] at hstep_len ⊢; omega
  have hfold_fan : ∀ (gs : List Gate) (env : List (Sum Bool ℕ)) (em : List Gate),
      (∀ g ∈ em, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
      ∀ g ∈ (gs.foldl stepOne (env, em)).2,
        (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro gs
    induction gs with
    | nil => intro env em hem; exact hem
    | cons g rest ih =>
      intro env em hem
      apply ih
      intro g' hg'
      dsimp only [stepOne] at hg'
      cases hopt : (stepGate env (9 + em.length) g).2 with
      | none => rw [hopt] at hg'; exact hem g' hg'
      | some gnew =>
        rw [hopt] at hg'
        simp only [List.mem_append, List.mem_singleton] at hg'
        rcases hg' with hg' | rfl
        · exact hem g' hg'
        · exact hstep_fan env (9 + em.length) g g' hopt
  have hfold_sem : ∀ (y : Fin 9 → Bool) (gs : List Gate) (env : List (Sum Bool ℕ)) (em : List Gate)
      (W_in : List Bool),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
      env.length = W_in.length →
      (∀ s ∈ env, Sum.elim (fun _ => True)
        (fun u => u < (em.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn y)).length) s) →
      (∀ w, W_in.getD w false =
        valOf (em.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn y))
          (env.getD w (Sum.inl false))) →
      ∀ w, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W_in).getD w false =
        valOf ((gs.foldl stepOne (env, em)).2.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn y))
          ((gs.foldl stepOne (env, em)).1.getD w (Sum.inl false)) := by
    intro y gs
    induction gs with
    | nil => intro env em W_in _ _ _ hagr; exact hagr
    | cons g rest ih =>
      intro env em W_in hgs hlen_eq hlt_env hagr
      obtain ⟨hop, hglen⟩ := hgs g (by simp)
      let W_out := em.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn y)
      have hW_out_len : W_out.length = 9 + em.length := by
        obtain ⟨ext, hext, hl⟩ := hfold_wires_prefix em (List.ofFn y)
        dsimp only [W_out]
        rw [hext, List.length_append, List.length_ofFn, hl]
      have hs := hstep_sem env W_in W_out g hop hglen hlen_eq hlt_env hagr
      rw [hW_out_len] at hs
      obtain ⟨hlen', hlt', hagr'⟩ := hs
      have hW_out'_eq :
          (stepOne (env, em) g).2.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn y) =
          Option.rec W_out (fun g' => W_out ++ [g'.op.eval (g'.inputs.map fun i => W_out.getD i false)])
            (stepGate env (9 + em.length) g).2 := by
        dsimp only [stepOne]
        cases (stepGate env (9 + em.length) g).2 with
        | none => rfl
        | some g' => simp [List.foldl_append, W_out]
      rw [← hW_out'_eq] at hlt' hagr'
      simpa only [List.foldl_cons] using
        ih (stepOne (env, em) g).1 (stepOne (env, em) g).2
          (W_in ++ [g.op.eval (g.inputs.map fun i => W_in.getD i false)])
          (fun g' hg' => hgs g' (by simp [hg'])) hlen' hlt' hagr'
  obtain ⟨finalEnv, emitted, hstFinal⟩ :
      ∃ e m, C.gates.foldl stepOne (env0, []) = (e, m) := ⟨_, _, rfl⟩
  have henv0_mid : ∀ i < 9, env0.getD (i + 1) (Sum.inl false) = Sum.inr i := by
    intro i hi; interval_cases i <;> rfl
  have hsem_all : ∀ (y : Fin 9 → Bool) (w : ℕ),
      (C.wires (List.ofFn (Fin.cons false y) ++ [true])).getD w false =
      valOf ((Circuit.mk emitted 0).wires (List.ofFn y)) (finalEnv.getD w (Sum.inl false)) := by
    intro y w
    rw [wires_def, wires_def]
    have h1 := hfold_sem y C.gates env0 [] (List.ofFn (Fin.cons false y) ++ [true])
      (hfan_cases C hfan) (by simp [env0])
    rw [hstFinal] at h1
    apply h1
    · intro s hs
      simp only [List.foldl_nil, List.length_ofFn]
      dsimp only [env0] at hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · trivial
      · exact (by omega : (0 : ℕ) < 9)
      · exact (by omega : (1 : ℕ) < 9)
      · exact (by omega : (2 : ℕ) < 9)
      · exact (by omega : (3 : ℕ) < 9)
      · exact (by omega : (4 : ℕ) < 9)
      · exact (by omega : (5 : ℕ) < 9)
      · exact (by omega : (6 : ℕ) < 9)
      · exact (by omega : (7 : ℕ) < 9)
      · exact (by omega : (8 : ℕ) < 9)
      · trivial
    · intro k
      simp only [List.foldl_nil]
      by_cases h0 : k = 0
      · subst h0
        rw [getD_app_lt _ _ _ _ (by simp)]
        simp [List.getD_eq_getElem?_getD, env0, valOf]
      · by_cases h10 : k = 10
        · subst h10
          rw [getD_app_ge _ _ _ _ (by simp)]
          rfl
        · by_cases h11 : k < 11
          · obtain ⟨i, hi_eq⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
            subst hi_eq
            have hi9 : i < 9 := by omega
            rw [getD_app_lt _ _ _ _ (by simp; omega), henv0_mid i hi9]
            dsimp only [valOf]
            rw [Sum.elim_inr]
            simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, show i + 1 < 10 by omega,
              hi9, ↓reduceDIte, Option.getD_some]
            exact Fin.cons_succ (α := fun _ => Bool) false y ⟨i, hi9⟩
          · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp [env0]; omega)]
            rfl
  have hout_inr : ∃ u, finalEnv.getD C.output (Sum.inl false) = Sum.inr u := by
    cases h : finalEnv.getD C.output (Sum.inl false) with
    | inr u => exact ⟨u, rfl⟩
    | inl b =>
      obtain ⟨y, hy⟩ := hp10_not_const_false0 b
      have hev := hC (Fin.cons false y)
      rw [Fin.cons_zero] at hev
      change C.eval (List.ofFn (Fin.cons false y) ++ [true]) = p10 (Fin.cons false y) at hev
      rw [eval_def, hsem_all y C.output, h] at hev
      exact False.elim (hy hev.symm)
  obtain ⟨uOut, huOut⟩ := hout_inr
  have hD9_ge16 : 16 ≤ emitted.length := by
    by_contra hlt16
    let D9 : Circuit := Circuit.mk emitted uOut
    have hD9fan : FanInTwo D9 := by
      intro g hg
      have hf := hfold_fan C.gates env0 [] (fun _ h => by cases h) g
      rw [hstFinal] at hf
      exact hf hg
    have hD9sz : D9.size ≤ 15 := by rw [size_def]; dsimp only [D9]; omega
    obtain ⟨y, hy⟩ := hP9Le15 D9 hD9fan hD9sz
    have hD9eq : D9.eval (List.ofFn y) = p9 y := by
      have hev := hC (Fin.cons false y)
      rw [Fin.cons_zero] at hev
      change C.eval (List.ofFn (Fin.cons false y) ++ [true]) = p10 (Fin.cons false y) at hev
      rw [hp10_cons_false, eval_def, hsem_all y C.output, huOut] at hev
      exact hev
    exact hy hD9eq
  have hem_bound : emitted.length + x4 ≤ C.gates.length := by
    have h := hfold_bound C.gates env0 [] (hfan_cases C hfan) (by simp [env0]) rfl rfl
    rw [hstFinal, List.length_nil, Nat.zero_add] at h
    exact h
  have hCsz18 : C.size = 18 := by
    have h18 : 18 ≤ C.gates.length := by
      have h := hem_bound
      rw [hx2] at h
      exact le_trans (Nat.add_le_add_right hD9_ge16 2) h
    have hsz' : C.gates.length ≤ 18 := hsz
    exact Nat.le_antisymm hsz' h18
  have hem16 : emitted.length = 16 := by
    have h := hem_bound
    rw [hx2] at h
    have hlen18 : C.gates.length = 18 := hCsz18
    rw [hlen18] at h
    exact Nat.le_antisymm (Nat.le_of_add_le_add_right h) hD9_ge16
  have hnon_eff_emits : ∀ k (hk : k < C.gates.length),
      eff010 C.gates[k] = false →
      (stepGate ((C.gates.take k).foldl stepOne (env0, [])).1
        (9 + ((C.gates.take k).foldl stepOne (env0, [])).2.length) C.gates[k]).2.isSome = true := by
    intro k hk hkf
    let stk := (C.gates.take k).foldl stepOne (env0, [])
    change (stepGate stk.1 (9 + stk.2.length) C.gates[k]).2.isSome = true
    cases hopt : (stepGate stk.1 (9 + stk.2.length) C.gates[k]).2 with
    | some _ => rfl
    | none =>
      have hsplit : C.gates = C.gates.take k ++ C.gates[k] :: C.gates.drop (k + 1) := by
        have h1 := List.take_append_drop k C.gates
        rw [List.drop_eq_getElem_cons hk] at h1
        exact h1.symm
      have hb1 : stk.2.length + List.countP eff010 (C.gates.take k) ≤ k := by
        have := hfold_bound (C.gates.take k) env0 []
          (fun g hg => hfan_cases C hfan g (List.mem_of_mem_take hg)) (by simp [env0]) rfl rfl
        have htklen : (C.gates.take k).length = k := List.length_take_of_le (by omega)
        simpa [stk, htklen] using this
      obtain ⟨extk, hextk, hlenk⟩ := hfold_prefix (C.gates.take k) env0 []
      have hstk1_len : 11 ≤ stk.1.length := by change stk.1 = env0 ++ extk at hextk; rw [hextk]; simp [env0]
      have hstk1_0 : stk.1.getD 0 (Sum.inl false) = Sum.inl false := by
        change stk.1 = env0 ++ extk at hextk; rw [hextk, getD_app_lt _ _ _ _ (by simp [env0])]; rfl
      have hstk1_10 : stk.1.getD 10 (Sum.inl false) = Sum.inl true := by
        change stk.1 = env0 ++ extk at hextk; rw [hextk, getD_app_lt _ _ _ _ (by simp [env0])]; rfl
      have hst1_eq : stepOne stk C.gates[k] = (stk.1 ++ [(stepGate stk.1 (9 + stk.2.length) C.gates[k]).1], stk.2) := by
        dsimp only [stepOne]
        rw [hopt]
      have hb2 : ((C.gates.drop (k + 1)).foldl stepOne (stepOne stk C.gates[k])).2.length +
          List.countP eff010 (C.gates.drop (k + 1)) ≤ stk.2.length + (C.gates.drop (k + 1)).length := by
        have := hfold_bound (C.gates.drop (k + 1)) (stepOne stk C.gates[k]).1 (stepOne stk C.gates[k]).2
          (fun g hg => hfan_cases C hfan g (List.mem_of_mem_drop hg))
          (by rw [hst1_eq]; simp; omega)
          (by rw [hst1_eq]; dsimp only; rw [getD_app_lt _ _ _ _ (by omega)]; exact hstk1_0)
          (by rw [hst1_eq]; dsimp only; rw [getD_app_lt _ _ _ _ (by omega)]; exact hstk1_10)
        simpa [hst1_eq] using this
      have hst_eq : (finalEnv, emitted) = (C.gates.drop (k + 1)).foldl stepOne (stepOne stk C.gates[k]) := by
        rw [← hstFinal]
        conv_lhs => rw [hsplit]
        rw [List.foldl_append, List.foldl_cons]
      have hcnt_eq : x4 = List.countP eff010 (C.gates.take k) + List.countP eff010 (C.gates.drop (k + 1)) := by
        change List.countP eff010 C.gates = _
        conv_lhs => rw [hsplit]
        rw [List.countP_append, List.countP_cons, hkf]
        simp
      have hdlen : (C.gates.drop (k + 1)).length = C.gates.length - (k + 1) := List.length_drop
      rw [← hst_eq] at hb2
      dsimp only at hb2
      have hlen18 : C.gates.length = 18 := hCsz18
      rw [hx2] at hcnt_eq
      rw [hem16] at hb2
      rw [hlen18] at hk hdlen
      rw [hdlen] at hb2
      have htot : 16 + (List.countP eff010 (C.gates.take k) + List.countP eff010 (C.gates.drop (k + 1))) ≤
          k + (18 - (k + 1)) := by
        have hsum := Nat.add_le_add hb1 hb2
        clear * - hsum
        omega
      rw [← hcnt_eq] at htot
      clear * - htot hk
      omega
  have hfinal_at : ∀ k (hk : k < C.gates.length),
      finalEnv.getD (11 + k) (Sum.inl false) =
      (stepGate ((C.gates.take k).foldl stepOne (env0, [])).1
        (9 + ((C.gates.take k).foldl stepOne (env0, [])).2.length) C.gates[k]).1 := by
    intro k hk
    let stk := (C.gates.take k).foldl stepOne (env0, [])
    have hsplit : C.gates = C.gates.take k ++ C.gates[k] :: C.gates.drop (k + 1) := by
      have h1 := List.take_append_drop k C.gates
      rw [List.drop_eq_getElem_cons hk] at h1
      exact h1.symm
    obtain ⟨extk, hextk, hlenk⟩ := hfold_prefix (C.gates.take k) env0 []
    have htklen : (C.gates.take k).length = k := List.length_take_of_le (by omega)
    have hstk_len : stk.1.length = 11 + k := by
      change stk.1 = env0 ++ extk at hextk
      rw [hextk, List.length_append, hlenk, htklen]; rfl
    obtain ⟨extr, hextr, _⟩ := hfold_prefix (C.gates.drop (k + 1)) (stepOne stk C.gates[k]).1 (stepOne stk C.gates[k]).2
    have hfe : finalEnv = (stk.1 ++ [(stepGate stk.1 (9 + stk.2.length) C.gates[k]).1]) ++ extr := by
      have h0 : finalEnv = (C.gates.foldl stepOne (env0, [])).1 := by rw [hstFinal]
      rw [h0]
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
      exact hextr
    rw [hfe, getD_app_lt _ _ _ _ (by simp [hstk_len]), getD_app_ge _ _ _ _ (by omega)]
    simp only [hstk_len, Nat.sub_self, List.getD_cons_zero]
    rfl
  have hpref_agree : ∀ k (hk : k < C.gates.length) w, w < 11 + k →
      ((C.gates.take k).foldl stepOne (env0, [])).1.getD w (Sum.inl false) =
      finalEnv.getD w (Sum.inl false) := by
    intro k hk w hw
    let stk := (C.gates.take k).foldl stepOne (env0, [])
    have hsplit : C.gates = C.gates.take k ++ C.gates.drop k := (List.take_append_drop k C.gates).symm
    obtain ⟨extk, hextk, hlenk⟩ := hfold_prefix (C.gates.take k) env0 []
    have htklen : (C.gates.take k).length = k := List.length_take_of_le (by omega)
    have hstk_len : stk.1.length = 11 + k := by
      change stk.1 = env0 ++ extk at hextk
      rw [hextk, List.length_append, hlenk, htklen]; rfl
    obtain ⟨extr, hextr, _⟩ := hfold_prefix (C.gates.drop k) stk.1 stk.2
    have hfe : finalEnv = stk.1 ++ extr := by
      have h0 : finalEnv = (C.gates.foldl stepOne (env0, [])).1 := by rw [hstFinal]
      rw [h0]
      conv_lhs => rw [hsplit]
      rw [List.foldl_append]
      exact hextr
    rw [hfe, getD_app_lt _ _ _ _ (by omega)]
  have hdead_kill : ∀ (j : ℕ) (hj : j < C.gates.length),
      eff010 C.gates[j] = true →
      C.output ≠ 11 + j →
      (∀ m (hm : m < C.gates.length), j < m → effReads (11 + j) C.gates[m] = false) →
      False := by
    intro j hj hj_eff hout_ne hno_read
    let D' : Circuit := Circuit.mk (C.gates.set j (Gate.mk GateOp.and [])) C.output
    have hD'fan : FanInTwo D' := by
      intro g hg
      dsimp only [D'] at hg
      rw [List.mem_iff_getElem] at hg
      obtain ⟨i, hi, rfl⟩ := hg
      have hi' : i < C.gates.length := by rw [List.length_set] at hi; exact hi
      by_cases hij : i = j
      · subst hij
        rw [List.getElem_set_self hi]
        exact ⟨Or.inl rfl, by simp⟩
      · rw [List.getElem_set_ne (by omega : j ≠ i) hi]
        exact hfan_cases C hfan C.gates[i] (List.getElem_mem hi')
    have hD'sz : D'.size ≤ 18 := by
      have hsz' : C.gates.length ≤ 18 := hsz
      change (C.gates.set j (Gate.mk GateOp.and [])).length ≤ 18
      rw [List.length_set]
      exact hsz'
    have hD'cnt : List.countP eff010 D'.gates = 1 := by
      have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
        have h1 := List.take_append_drop j C.gates
        rw [List.drop_eq_getElem_cons hj] at h1
        exact h1.symm
      have hset_eq : C.gates.set j (Gate.mk GateOp.and []) =
          C.gates.take j ++ Gate.mk GateOp.and [] :: C.gates.drop (j + 1) := by
        have htklen : (C.gates.take j).length = j := List.length_take_of_le (by omega)
        apply List.ext_getElem
        · simp [htklen]; omega
        · intro i hi1 hi2
          by_cases hlt : i < j
          · rw [List.getElem_set_ne (by omega) (by omega), List.getElem_append_left (by omega), List.getElem_take]
          · by_cases heq : i = j
            · subst heq
              rw [List.getElem_set_self (by omega), List.getElem_append_right (by omega)]
              simp [htklen]
            · rw [List.getElem_set_ne (by omega) (by omega), List.getElem_append_right (by omega)]
              have hm : i - (C.gates.take j).length = (i - j - 1) + 1 := by omega
              simp only [hm, List.getElem_cons_succ, List.getElem_drop]
              congr 1; omega
      dsimp only [D']
      rw [hset_eq, List.countP_append, List.countP_cons]
      have h0 : eff010 (Gate.mk GateOp.and []) = false := rfl
      rw [h0]
      have hcx : x4 = List.countP eff010 (C.gates.take j) + 1 + List.countP eff010 (C.gates.drop (j + 1)) := by
        change List.countP eff010 C.gates = _
        conv_lhs => rw [hsplit]
        rw [List.countP_append, List.countP_cons, hj_eff]
        simp only [↓reduceIte]
        clear * -
        omega
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      rw [hx2] at hcx
      clear * - hcx
      omega
    have hD'comp : ∀ x : Fin 10 → Bool, D'.eval (List.ofFn x ++ [!x 0]) = p10 x := by
      intro x
      dsimp only [p10]
      rw [← hC x, eval_def, eval_def, wires_def, wires_def]
      dsimp only [D']
      let xs := List.ofFn x ++ [!x 0]
      have hW_eq : ∀ k ≤ C.gates.length,
          (((C.gates.set j (Gate.mk GateOp.and [])).take k).foldl
            (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs).length = 11 + k ∧
          ((C.gates.take k).foldl
            (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs).length = 11 + k ∧
          ∀ w, w ≠ 11 + j →
            (((C.gates.set j (Gate.mk GateOp.and [])).take k).foldl
              (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs).getD w false =
            ((C.gates.take k).foldl
              (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs).getD w false := by
        intro k
        induction k with
        | zero => intro _; refine ⟨by simp [xs], by simp [xs], fun _ _ => rfl⟩
        | succ k ih =>
          intro hk
          obtain ⟨hl1, hl2, hagr⟩ := ih (by omega)
          have hset_len : (C.gates.set j (Gate.mk GateOp.and [])).length = C.gates.length := List.length_set
          have htk1 : (C.gates.set j (Gate.mk GateOp.and [])).take (k + 1) =
              (C.gates.set j (Gate.mk GateOp.and [])).take k ++ [(C.gates.set j (Gate.mk GateOp.and []))[k]'(by omega)] :=
            List.take_succ_eq_append_getElem (by omega)
          have htk2 : C.gates.take (k + 1) = C.gates.take k ++ [C.gates[k]] :=
            List.take_succ_eq_append_getElem (by omega)
          let W1 := ((C.gates.set j (Gate.mk GateOp.and [])).take k).foldl
            (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs
          let W2 := (C.gates.take k).foldl
            (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs
          let g1 := (C.gates.set j (Gate.mk GateOp.and []))[k]'(by omega)
          let g2 := C.gates[k]
          simp only [htk1, htk2, List.foldl_append, List.foldl_cons, List.foldl_nil]
          change (W1 ++ [g1.op.eval (g1.inputs.map fun i => W1.getD i false)]).length = 11 + (k + 1) ∧
            (W2 ++ [g2.op.eval (g2.inputs.map fun i => W2.getD i false)]).length = 11 + (k + 1) ∧
            ∀ w, w ≠ 11 + j →
              (W1 ++ [g1.op.eval (g1.inputs.map fun i => W1.getD i false)]).getD w false =
              (W2 ++ [g2.op.eval (g2.inputs.map fun i => W2.getD i false)]).getD w false
          change W1.length = 11 + k at hl1
          change W2.length = 11 + k at hl2
          refine ⟨by rw [List.length_append, List.length_singleton, hl1]; omega,
            by rw [List.length_append, List.length_singleton, hl2]; omega, ?_⟩
          intro w hw
          by_cases hlt : w < 11 + k
          · rw [getD_app_lt _ _ _ _ (by omega), getD_app_lt _ _ _ _ (by omega)]
            exact hagr w hw
          · by_cases heq : w = 11 + k
            · subst heq
              have hg_eq : g1 = g2 := List.getElem_set_ne (by omega : j ≠ k) (by omega)
              rw [hg_eq, getD_app_ge _ _ _ _ (by omega), getD_app_ge _ _ _ _ (by omega)]
              simp only [hl1, hl2, Nat.sub_self, List.getD_cons_zero]
              apply hgate_eval_congr g2 W1 W2 (hfan_cases C hfan g2 (List.getElem_mem (by omega))).1
              intro u hu
              by_cases hu_eq : u = 11 + j
              · subst hu_eq
                by_cases hltj : k < j
                · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
                · have hgt : j < k := by omega
                  have := hno_read k (by omega) hgt
                  rw [this] at hu
                  cases hu
              · exact hagr u hu_eq
            · rw [List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton, hl1]; omega),
                List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton, hl2]; omega)]
      obtain ⟨_, _, hagr_all⟩ := hW_eq C.gates.length (le_refl _)
      have hset_len : (C.gates.set j (Gate.mk GateOp.and [])).length = C.gates.length := List.length_set
      rw [List.take_length, ← hset_len, List.take_length] at hagr_all
      exact hagr_all C.output hout_ne
    exact hDeg1 D' hD'fan hD'sz hD'cnt hD'comp
  have hex_two : ∃ (j1 j2 : ℕ) (h12 : j1 < j2) (h2lt : j2 < C.gates.length),
      eff010 (C.gates[j1]'(by omega)) = true ∧ eff010 (C.gates[j2]'h2lt) = true ∧
      ∀ m (hm : m < C.gates.length), eff010 C.gates[m] = true → m = j1 ∨ m = j2 := by
    have haux : ∀ (gs : List Gate), List.countP eff010 gs = 2 →
        ∃ (j1 j2 : ℕ) (h12 : j1 < j2) (h2lt : j2 < gs.length),
          eff010 (gs[j1]'(by omega)) = true ∧ eff010 (gs[j2]'h2lt) = true ∧
          ∀ m (hm : m < gs.length), eff010 gs[m] = true → m = j1 ∨ m = j2 := by
      intro gs
      induction gs with
      | nil => intro h; simp at h
      | cons g rest ih =>
        intro h
        rw [List.countP_cons] at h
        cases hg : eff010 g
        · rw [hg] at h
          simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h
          obtain ⟨j1, j2, h12, h2lt, hj1, hj2, hall⟩ := ih h
          refine ⟨j1 + 1, j2 + 1, by omega, by simp; omega, by simpa using hj1, by simpa using hj2, ?_⟩
          intro m hm hme
          cases m with
          | zero => simp [hg] at hme
          | succ m' =>
            rcases hall m' (by simp at hm; omega) (by simpa using hme) with rfl | rfl
            · left; rfl
            · right; rfl
        · rw [hg] at h
          simp only [↓reduceIte] at h
          have hcnt1 : List.countP eff010 rest = 1 := by omega
          have h1 : ∃ (j2 : ℕ) (h2lt : j2 < rest.length), eff010 (rest[j2]'h2lt) = true ∧
              ∀ m (hm : m < rest.length), eff010 rest[m] = true → m = j2 := by
            clear ih h hg
            induction rest with
            | nil => simp at hcnt1
            | cons g' rest' ih' =>
              rw [List.countP_cons] at hcnt1
              cases hg' : eff010 g'
              · rw [hg'] at hcnt1
                simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hcnt1
                obtain ⟨j2, h2lt, hj2, hall'⟩ := ih' hcnt1
                refine ⟨j2 + 1, by simp; omega, by simpa using hj2, ?_⟩
                intro m hm hme
                cases m with
                | zero => simp [hg'] at hme
                | succ m' =>
                  have := hall' m' (by simp at hm; omega) (by simpa using hme)
                  omega
              · rw [hg'] at hcnt1
                simp only [↓reduceIte] at hcnt1
                have h0 : List.countP eff010 rest' = 0 := by omega
                refine ⟨0, by simp, by simpa using hg', ?_⟩
                intro m hm hme
                cases m with
                | zero => rfl
                | succ m' =>
                  have hm' : m' < rest'.length := by simp at hm; omega
                  have := List.countP_eq_zero.mp h0 rest'[m'] (List.getElem_mem hm')
                  exact False.elim (this (by simpa using hme))
          obtain ⟨j2, h2lt, hj2, hall'⟩ := h1
          refine ⟨0, j2 + 1, by omega, by simp; omega, by simpa using hg, by simpa using hj2, ?_⟩
          intro m hm hme
          cases m with
          | zero => left; rfl
          | succ m' => right; have := hall' m' (by simp at hm; omega) (by simpa using hme); omega
    exact haux C.gates hx2
  obtain ⟨j1, j2, hj12, hj2lt, hj1_eff, hj2_eff, hj_only⟩ := hex_two
  have hno_const_j2 : ∀ b, finalEnv.getD (11 + j2) (Sum.inl false) ≠ Sum.inl b := by
    intro b hb
    apply hdead_kill j2 hj2lt hj2_eff
    · intro hEq; rw [hEq, hb] at huOut; cases huOut
    · intro m hm hgt
      cases hr : effReads (11 + j2) C.gates[m]
      · rfl
      · have hm_ne : eff010 C.gates[m] = false := by
          cases he : eff010 C.gates[m]
          · rfl
          · rcases hj_only m hm he with rfl | rfl <;> omega
        have hem_some := hnon_eff_emits m hm hm_ne
        let stm := (C.gates.take m).foldl stepOne (env0, [])
        have hlook : stm.1.getD (11 + j2) (Sum.inl false) = Sum.inl b := by
          rw [hpref_agree m hm (11 + j2) (by omega), hb]
        have hnone := hstep_const_none stm.1 (9 + stm.2.length) C.gates[m] (11 + j2) b
          (hfan_cases C hfan C.gates[m] (List.getElem_mem hm)).1
          (hfan_cases C hfan C.gates[m] (List.getElem_mem hm)).2 hr hlook
        change (stepGate stm.1 (9 + stm.2.length) C.gates[m]).2.isSome = true at hem_some
        rw [hnone] at hem_some
        cases hem_some
  have hno_const_j1 : ∀ b, finalEnv.getD (11 + j1) (Sum.inl false) ≠ Sum.inl b := by
    intro b hb
    by_cases h2reads : effReads (11 + j1) C.gates[j2] = true
    · let st2 := (C.gates.take j2).foldl stepOne (env0, [])
      have hlook1 : st2.1.getD (11 + j1) (Sum.inl false) = Sum.inl b := by
        rw [hpref_agree j2 hj2lt (11 + j1) (by omega), hb]
      have hlook0 : st2.1.getD 0 (Sum.inl false) = Sum.inl false := by
        obtain ⟨ext, hext, _⟩ := hfold_prefix (C.gates.take j2) env0 []
        change st2.1 = env0 ++ ext at hext
        rw [hext, getD_app_lt _ _ _ _ (by simp [env0])]; rfl
      have hlook10 : st2.1.getD 10 (Sum.inl false) = Sum.inl true := by
        obtain ⟨ext, hext, _⟩ := hfold_prefix (C.gates.take j2) env0 []
        change st2.1 = env0 ++ ext at hext
        rw [hext, getD_app_lt _ _ _ _ (by simp [env0])]; rfl
      obtain ⟨hop2, hlen2⟩ := hfan_cases C hfan C.gates[j2] (List.getElem_mem hj2lt)
      have hj2_inl : ∃ b2, (stepGate st2.1 (9 + st2.2.length) C.gates[j2]).1 = Sum.inl b2 := by
        obtain ⟨op2, ins2, hgk2⟩ : ∃ op2 ins2, C.gates[j2] = Gate.mk op2 ins2 :=
          ⟨C.gates[j2].op, C.gates[j2].inputs, rfl⟩
        rw [hgk2] at hop2 hlen2 h2reads ⊢
        have h010 := hj2_eff
        rw [hgk2] at h010
        rcases hop2 with rfl | rfl | rfl
        · dsimp only [effReads, eff010] at h2reads h010
          rw [eval_and_f] at h2reads h010
          simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true, List.contains_eq_mem,
            decide_eq_true_eq] at h2reads h010
          cases ins2 with
          | nil => exact ⟨true, rfl⟩
          | cons a rest =>
            cases rest with
            | nil =>
              simp only [List.mem_singleton] at h2reads
              subst h2reads
              exact ⟨b, by dsimp only [stepGate]; rw [hlook1]⟩
            | cons c rest2 =>
              cases rest2 with
              | nil =>
                simp only [List.mem_cons, List.not_mem_nil, or_false] at h2reads h010
                dsimp only [stepGate]
                rcases h2reads with rfl | rfl
                · rcases h010 with (hbad | rfl) | (hbad | rfl)
                  · omega
                  · rw [hlook1, hlook0]; cases b <;> exact ⟨false, rfl⟩
                  · omega
                  · rw [hlook1, hlook10]; cases b
                    · exact ⟨false, rfl⟩
                    · exact ⟨true, rfl⟩
                · rcases h010 with (rfl | hbad) | (rfl | hbad)
                  · rw [hlook0]; exact ⟨false, rfl⟩
                  · omega
                  · rw [hlook10, hlook1]; exact ⟨b, rfl⟩
                  · omega
              | cons d rest3 => simp at hlen2
        · dsimp only [effReads, eff010] at h2reads h010
          rw [eval_or_f] at h2reads h010
          simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true, List.contains_eq_mem,
            decide_eq_true_eq] at h2reads h010
          cases ins2 with
          | nil => exact ⟨false, rfl⟩
          | cons a rest =>
            cases rest with
            | nil =>
              simp only [List.mem_singleton] at h2reads
              subst h2reads
              exact ⟨b, by dsimp only [stepGate]; rw [hlook1]⟩
            | cons c rest2 =>
              cases rest2 with
              | nil =>
                simp only [List.mem_cons, List.not_mem_nil, or_false] at h2reads h010
                dsimp only [stepGate]
                rcases h2reads with rfl | rfl
                · rcases h010 with (hbad | rfl) | (hbad | rfl)
                  · omega
                  · rw [hlook1, hlook0]; cases b
                    · exact ⟨false, rfl⟩
                    · exact ⟨true, rfl⟩
                  · omega
                  · rw [hlook1, hlook10]; cases b <;> exact ⟨true, rfl⟩
                · rcases h010 with (rfl | hbad) | (rfl | hbad)
                  · rw [hlook0, hlook1]; exact ⟨b, rfl⟩
                  · omega
                  · rw [hlook10]; exact ⟨true, rfl⟩
                  · omega
              | cons d rest3 => simp at hlen2
        · dsimp only [effReads, eff010] at h2reads h010
          rw [eval_not_f] at h2reads h010
          simp only [↓reduceIte, Bool.or_eq_true, beq_iff_eq] at h2reads h010
          rw [h2reads] at h010
          simp only [Option.some.injEq] at h010
          rcases h010 with h | h <;> omega
      obtain ⟨b2, hb2⟩ := hj2_inl
      have hfin2 := hfinal_at j2 hj2lt
      rw [hb2] at hfin2
      exact hno_const_j2 b2 hfin2
    · apply hdead_kill j1 (by omega) hj1_eff
      · intro hEq; rw [hEq, hb] at huOut; cases huOut
      · intro m hm hgt
        by_cases hmj2 : m = j2
        · have hnr : effReads (11 + j1) C.gates[j2] = false := by
            cases hr : effReads (11 + j1) C.gates[j2]
            · rfl
            · exact False.elim (h2reads hr)
          subst hmj2
          exact hnr
        · cases hr : effReads (11 + j1) C.gates[m]
          · rfl
          · have hm_ne : eff010 C.gates[m] = false := by
              cases he : eff010 C.gates[m]
              · rfl
              · rcases hj_only m hm he with rfl | rfl <;> omega
            have hem_some := hnon_eff_emits m hm hm_ne
            let stm := (C.gates.take m).foldl stepOne (env0, [])
            have hlook : stm.1.getD (11 + j1) (Sum.inl false) = Sum.inl b := by
              rw [hpref_agree m hm (11 + j1) (by omega), hb]
            have hnone := hstep_const_none stm.1 (9 + stm.2.length) C.gates[m] (11 + j1) b
              (hfan_cases C hfan C.gates[m] (List.getElem_mem hm)).1
              (hfan_cases C hfan C.gates[m] (List.getElem_mem hm)).2 hr hlook
            change (stepGate stm.1 (9 + stm.2.length) C.gates[m]).2.isSome = true at hem_some
            rw [hnone] at hem_some
            cases hem_some
  have hshape : ∀ g ∈ C.gates, eff010 g = true →
      (g.op = GateOp.and ∧ ∃ w, w ≠ 0 ∧ w ≠ 10 ∧ (g.inputs = [10, w] ∨ g.inputs = [w, 10])) ∨
      (g.op = GateOp.or ∧ ∃ w, w ≠ 0 ∧ w ≠ 10 ∧ (g.inputs = [0, w] ∨ g.inputs = [w, 0])) := by
    intro g hg heff
    rw [List.mem_iff_getElem] at hg
    obtain ⟨k, hk, rfl⟩ := hg
    have hno_inl : ∀ b, finalEnv.getD (11 + k) (Sum.inl false) ≠ Sum.inl b := by
      rcases hj_only k hk heff with rfl | rfl
      · exact hno_const_j1
      · exact hno_const_j2
    let stk := (C.gates.take k).foldl stepOne (env0, [])
    have hstep_no_inl : ∀ b, (stepGate stk.1 (9 + stk.2.length) C.gates[k]).1 ≠ Sum.inl b := by
      intro b hb
      have hfin := hfinal_at k hk
      rw [hb] at hfin
      exact hno_inl b hfin
    have hlook0 : stk.1.getD 0 (Sum.inl false) = Sum.inl false := by
      obtain ⟨ext, hext, _⟩ := hfold_prefix (C.gates.take k) env0 []
      change stk.1 = env0 ++ ext at hext
      rw [hext, getD_app_lt _ _ _ _ (by simp [env0])]; rfl
    have hlook10 : stk.1.getD 10 (Sum.inl false) = Sum.inl true := by
      obtain ⟨ext, hext, _⟩ := hfold_prefix (C.gates.take k) env0 []
      change stk.1 = env0 ++ ext at hext
      rw [hext, getD_app_lt _ _ _ _ (by simp [env0])]; rfl
    obtain ⟨hop, hlen⟩ := hfan_cases C hfan C.gates[k] (List.getElem_mem hk)
    obtain ⟨opk, insk, hgk_eq⟩ : ∃ opk insk, C.gates[k] = Gate.mk opk insk :=
      ⟨C.gates[k].op, C.gates[k].inputs, rfl⟩
    rw [hgk_eq] at hop hlen heff hstep_no_inl ⊢
    rcases hop with rfl | rfl | rfl
    · left
      refine ⟨rfl, ?_⟩
      dsimp only [eff010] at heff
      rw [eval_and_f] at heff
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true, List.contains_eq_mem,
        decide_eq_true_eq] at heff
      cases insk with
      | nil => exact False.elim (hstep_no_inl true rfl)
      | cons a rest =>
        cases rest with
        | nil =>
          simp only [List.mem_singleton] at heff
          rcases heff with rfl | rfl
          · exact False.elim (hstep_no_inl false hlook0)
          · exact False.elim (hstep_no_inl true hlook10)
        | cons b rest2 =>
          cases rest2 with
          | nil =>
            have hne0_a : a ≠ 0 := by
              intro h0; subst h0
              exact hstep_no_inl false (by dsimp only [stepGate]; rw [hlook0]; rfl)
            have hne0_b : b ≠ 0 := by
              intro h0; subst h0
              apply hstep_no_inl false
              dsimp only [stepGate]
              cases ha : stk.1.getD a (Sum.inl false) with
              | inl ba =>
                dsimp only [Sum.elim_inl]
                cases ba
                · rfl
                · rw [hlook0]; rfl
              | inr u =>
                dsimp only [Sum.elim_inr]
                rw [hlook0]; rfl
            simp only [List.mem_cons, List.not_mem_nil, or_false] at heff
            rcases heff with (rfl | rfl) | (rfl | rfl)
            · exact False.elim (hne0_a rfl)
            · exact False.elim (hne0_b rfl)
            · have hb_ne10 : b ≠ 10 := by
                intro h10; subst h10
                exact hstep_no_inl true (by dsimp only [stepGate]; rw [hlook10]; rfl)
              exact ⟨b, hne0_b, hb_ne10, Or.inl rfl⟩
            · have ha_ne10 : a ≠ 10 := by
                intro h10; subst h10
                exact hstep_no_inl true (by dsimp only [stepGate]; rw [hlook10]; rfl)
              exact ⟨a, hne0_a, ha_ne10, Or.inr rfl⟩
          | cons c rest3 => simp at hlen
    · right
      refine ⟨rfl, ?_⟩
      dsimp only [eff010] at heff
      rw [eval_or_f] at heff
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true, List.contains_eq_mem,
        decide_eq_true_eq] at heff
      cases insk with
      | nil => exact False.elim (hstep_no_inl false rfl)
      | cons a rest =>
        cases rest with
        | nil =>
          simp only [List.mem_singleton] at heff
          rcases heff with rfl | rfl
          · exact False.elim (hstep_no_inl false hlook0)
          · exact False.elim (hstep_no_inl true hlook10)
        | cons b rest2 =>
          cases rest2 with
          | nil =>
            have hne10_a : a ≠ 10 := by
              intro h10; subst h10
              exact hstep_no_inl true (by dsimp only [stepGate]; rw [hlook10]; rfl)
            have hne10_b : b ≠ 10 := by
              intro h10; subst h10
              apply hstep_no_inl true
              dsimp only [stepGate]
              cases ha : stk.1.getD a (Sum.inl false) with
              | inl ba =>
                dsimp only [Sum.elim_inl]
                cases ba
                · rw [hlook10]; rfl
                · rfl
              | inr u =>
                dsimp only [Sum.elim_inr]
                rw [hlook10]; rfl
            simp only [List.mem_cons, List.not_mem_nil, or_false] at heff
            rcases heff with (rfl | rfl) | (rfl | rfl)
            · have hb_ne0 : b ≠ 0 := by
                intro h0; subst h0
                exact hstep_no_inl false (by dsimp only [stepGate]; rw [hlook0]; rfl)
              exact ⟨b, hb_ne0, hne10_b, Or.inl rfl⟩
            · have ha_ne0 : a ≠ 0 := by
                intro h0; subst h0
                exact hstep_no_inl false (by dsimp only [stepGate]; rw [hlook0]; rfl)
              exact ⟨a, ha_ne0, hne10_a, Or.inr rfl⟩
            · exact False.elim (hne10_a rfl)
            · exact False.elim (hne10_b rfl)
          | cons c rest3 => simp at hlen
    · dsimp only [eff010] at heff
      rw [eval_not_f] at heff
      simp only [↓reduceIte, Bool.or_eq_true, beq_iff_eq] at heff
      cases insk with
      | nil => simp at heff
      | cons a rest =>
        simp only [List.head?_cons, Option.some.injEq] at heff
        rcases heff with rfl | rfl
        · exact False.elim (hstep_no_inl true (by dsimp only [stepGate]; rw [hlook0]; rfl))
        · exact False.elim (hstep_no_inl false (by dsimp only [stepGate]; rw [hlook10]; rfl))
  obtain ⟨x, hx⟩ := hDeg2Exact18 C hfan hCsz18 hx2 hshape
  exact hx (hC x)
