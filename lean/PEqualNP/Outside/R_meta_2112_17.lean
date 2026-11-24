import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2112_17
    (hSoleNot :
      have p9 : (Fin 9 → Bool) → Bool := fun x =>
        decide (∃ a b : Fin 9, (([50, 68, 136, 272, 0, 384, 256] : List ℕ).getD a.val 0).testBit b.val = true ∧ x a = true ∧ x b = true)
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo D →
        D.size ≤ 14 →
        (∀ y : Fin 9 → Bool, D.eval (List.ofFn y) = p9 (Function.update y 4 (!y 4))) →
        False)
    (hSoleAndFromOr :
      have p9 : (Fin 9 → Bool) → Bool := fun x =>
        decide (∃ a b : Fin 9, (([50, 68, 136, 272, 0, 384, 256] : List ℕ).getD a.val 0).testBit b.val = true ∧ x a = true ∧ x b = true)
      have rd : (C : PEqualNP.CircuitLowerBounds.Circuit) → Fin 9 → Finset (Fin C.size) := fun C v =>
        Finset.univ.filter (fun i : Fin C.size => v.val ∈ (C.gates.get i).inputs)
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.IsMinimalCircuit 9 C →
        C.size ≤ 15 →
        PEqualNP.MetaComplexity.circuitFun 9 C = p9 →
        (∀ i : Fin C.size,
          have g : PEqualNP.CircuitLowerBounds.Gate := C.gates.get i
          (∀ u ∈ g.inputs, u < 9 + i.val) ∧ g.inputs.Nodup ∧
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1 ∨
            g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 2)) →
        (∀ v ∈ ([4, 6, 7] : List (Fin 9)),
          (rd C v).Nonempty ∧ (rd C v).card ≤ 2 ∧
          ((rd C v).card = 2 → ∀ i ∈ rd C v, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
        (∃ j k : Fin C.size, k < j ∧
          (∀ i : Fin C.size, 4 ∈ (C.gates.get i).inputs ↔ i = j) ∧
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          9 + k.val ∈ (C.gates.get j).inputs ∧
          (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          ∀ x : Fin 9 → Bool, x 4 = false → p9 x = false → (x 0 = true ∨ x 3 = true) →
            (C.wires (List.ofFn x)).getD (9 + k.val) false = true) →
        False)
    (hSoleAndFromAnd :
      have p9 : (Fin 9 → Bool) → Bool := fun x =>
        decide (∃ a b : Fin 9, (([50, 68, 136, 272, 0, 384, 256] : List ℕ).getD a.val 0).testBit b.val = true ∧ x a = true ∧ x b = true)
      have rd : (C : PEqualNP.CircuitLowerBounds.Circuit) → Fin 9 → Finset (Fin C.size) := fun C v =>
        Finset.univ.filter (fun i : Fin C.size => v.val ∈ (C.gates.get i).inputs)
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.IsMinimalCircuit 9 C →
        C.size ≤ 15 →
        PEqualNP.MetaComplexity.circuitFun 9 C = p9 →
        (∀ i : Fin C.size,
          have g : PEqualNP.CircuitLowerBounds.Gate := C.gates.get i
          (∀ u ∈ g.inputs, u < 9 + i.val) ∧ g.inputs.Nodup ∧
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1 ∨
            g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 2)) →
        (∀ v ∈ ([4, 6, 7] : List (Fin 9)),
          (rd C v).Nonempty ∧ (rd C v).card ≤ 2 ∧
          ((rd C v).card = 2 → ∀ i ∈ rd C v, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
        (∃ j k : Fin C.size, k < j ∧
          (∀ i : Fin C.size, 4 ∈ (C.gates.get i).inputs ↔ i = j) ∧
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          9 + k.val ∈ (C.gates.get j).inputs ∧
          (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          ∀ x : Fin 9 → Bool, x 4 = false → p9 x = false → (x 0 = true ∨ x 3 = true) →
            (C.wires (List.ofFn x)).getD (9 + k.val) false = true) →
        False)
    (hSoleAndFromNot :
      have p9 : (Fin 9 → Bool) → Bool := fun x =>
        decide (∃ a b : Fin 9, (([50, 68, 136, 272, 0, 384, 256] : List ℕ).getD a.val 0).testBit b.val = true ∧ x a = true ∧ x b = true)
      have rd : (C : PEqualNP.CircuitLowerBounds.Circuit) → Fin 9 → Finset (Fin C.size) := fun C v =>
        Finset.univ.filter (fun i : Fin C.size => v.val ∈ (C.gates.get i).inputs)
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.IsMinimalCircuit 9 C →
        C.size ≤ 15 →
        PEqualNP.MetaComplexity.circuitFun 9 C = p9 →
        (∀ i : Fin C.size,
          have g : PEqualNP.CircuitLowerBounds.Gate := C.gates.get i
          (∀ u ∈ g.inputs, u < 9 + i.val) ∧ g.inputs.Nodup ∧
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1 ∨
            g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 2)) →
        (∀ v ∈ ([4, 6, 7] : List (Fin 9)),
          (rd C v).Nonempty ∧ (rd C v).card ≤ 2 ∧
          ((rd C v).card = 2 → ∀ i ∈ rd C v, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
        (∃ j k : Fin C.size, k < j ∧
          (∀ i : Fin C.size, 4 ∈ (C.gates.get i).inputs ↔ i = j) ∧
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          9 + k.val ∈ (C.gates.get j).inputs ∧
          (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∀ x : Fin 9 → Bool, x 4 = false → p9 x = false → (x 0 = true ∨ x 3 = true) →
            (C.wires (List.ofFn x)).getD (9 + k.val) false = true) →
        False) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (x2 : PEqualNP.CircuitLowerBounds.Circuit) → Fin (9 : ℕ) → Finset (Fin x2.size) := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)) => {x4 : Fin x2.size | ↑x3 ∈ (x2.gates.get x4).inputs}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) =>   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x3 ∧     x3.size ≤ (15 : ℕ) ∧       PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 ∧         (∀ (x4 : Fin x3.size),             have x5 : PEqualNP.CircuitLowerBounds.Gate := x3.gates.get x4;             (∀ x6 ∈ x5.inputs, x6 < (9 : ℕ) + ↑x4) ∧ x5.inputs.Nodup ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (1 : ℕ) ∨ x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (2 : ℕ))) ∧           ∀ x4 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x3 x4).Nonempty ∧ (x2 x3 x4).card ≤ (2 : ℕ) ∧ ((x2 x3 x4).card = (2 : ℕ) → ∀ x7 ∈ x2 x3 x4, (x3.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → (∃ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], ∃ x7 ∈ x2 x4 x6, (x4.gates.get x7).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or) → False := by
  dsimp only
  intro C0 h30 hex0
  let edges : List (Fin 9 × Fin 9) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
  let mask : List ℕ := [50, 68, 136, 272, 0, 384, 256]
  let p9 : (Fin 9 → Bool) → Bool := fun x =>
    decide (∃ a b : Fin 9, (mask.getD a.val 0).testBit b.val = true ∧ x a = true ∧ x b = true)
  let p9e : (Fin 9 → Bool) → Bool := fun x => edges.any (fun e => x e.1 && x e.2)
  have hp9_x1 : (fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) = p9 := by
    funext x
    have h1 : (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) = p9e x := by
      simp only [p9e, edges, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
    rw [h1, Bool.eq_iff_iff]
    simp only [p9e, p9, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    have hfwd : ∀ e ∈ edges, (mask.getD e.1.val 0).testBit e.2.val = true ∨ (mask.getD e.2.val 0).testBit e.1.val = true := by decide
    have hbwd : ∀ a b : Fin 9, (mask.getD a.val 0).testBit b.val = true → (a, b) ∈ edges ∨ (b, a) ∈ edges := by decide
    constructor
    · rintro ⟨e, he, h1, h2⟩
      rcases hfwd e he with hm | hm
      · exact ⟨e.1, e.2, hm, h1, h2⟩
      · exact ⟨e.2, e.1, hm, h2, h1⟩
    · rintro ⟨a, b, hm, ha, hb⟩
      rcases hbwd a b hm with he | he
      · exact ⟨(a, b), he, ha, hb⟩
      · exact ⟨(b, a), he, hb, ha⟩
  let σ : Fin 9 → Fin 9 := fun i => ([1, 2, 3, 8, 6, 0, 7, 4, 5] : List (Fin 9)).getD i.val 0
  let τ : Fin 9 → Fin 9 := fun i => ([5, 0, 1, 2, 7, 8, 4, 6, 3] : List (Fin 9)).getD i.val 0
  have hστ : ∀ i : Fin 9, σ (τ i) = i := by decide
  have hτσ : ∀ i : Fin 9, τ (σ i) = i := by decide
  have hσ7 : σ 7 = 4 := by decide
  have hτ6 : τ 6 = 4 := by decide
  have hσ467 : ∀ i : Fin 9, i ∈ ([4, 6, 7] : List (Fin 9)) → σ i ∈ ([4, 6, 7] : List (Fin 9)) := by decide
  have hτ467 : ∀ i : Fin 9, i ∈ ([4, 6, 7] : List (Fin 9)) → τ i ∈ ([4, 6, 7] : List (Fin 9)) := by decide
  have hσ_adj : ∀ a b : Fin 9, (mask.getD a.val 0).testBit b.val = true →
      (mask.getD (σ a).val 0).testBit (σ b).val = true ∨ (mask.getD (σ b).val 0).testBit (σ a).val = true := by decide
  have hτ_adj : ∀ a b : Fin 9, (mask.getD a.val 0).testBit b.val = true →
      (mask.getD (τ a).val 0).testBit (τ b).val = true ∨ (mask.getD (τ b).val 0).testBit (τ a).val = true := by decide
  have hp9_perm (π πInv : Fin 9 → Fin 9) (h1 : ∀ i, π (πInv i) = i) (h2 : ∀ i, πInv (π i) = i)
      (hA : ∀ a b : Fin 9, (mask.getD a.val 0).testBit b.val = true →
        (mask.getD (π a).val 0).testBit (π b).val = true ∨ (mask.getD (π b).val 0).testBit (π a).val = true)
      (hB : ∀ a b : Fin 9, (mask.getD a.val 0).testBit b.val = true →
        (mask.getD (πInv a).val 0).testBit (πInv b).val = true ∨ (mask.getD (πInv b).val 0).testBit (πInv a).val = true)
      (x : Fin 9 → Bool) : p9 (fun i => x (π i)) = p9 x := by
    rw [Bool.eq_iff_iff]
    simp only [p9, decide_eq_true_eq]
    constructor
    · rintro ⟨a, b, hm, ha, hb⟩
      rcases hA a b hm with hm' | hm'
      · exact ⟨π a, π b, hm', ha, hb⟩
      · exact ⟨π b, π a, hm', hb, ha⟩
    · rintro ⟨a, b, hm, ha, hb⟩
      rcases hB a b hm with hm' | hm'
      · exact ⟨πInv a, πInv b, hm', by rw [h1]; exact ha, by rw [h1]; exact hb⟩
      · exact ⟨πInv b, πInv a, hm', by rw [h1]; exact hb, by rw [h1]; exact ha⟩
  let step : List Bool → Gate → List Bool := fun ws g =>
    ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  let run : List Gate → List Bool → List Bool := fun gs ws => gs.foldl step ws
  have hand_eval (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
    change (a && (b && true)) = (a && b)
    exact congrArg (a && ·) (Bool.and_true b)
  have getD_snoc_eq (l : List Bool) (a : Bool) : (l ++ [a]).getD l.length false = a := by
    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]
  have getD_snoc_ne (l : List Bool) (a : Bool) (j : ℕ) (hj : j ≠ l.length) :
      (l ++ [a]).getD j false = l.getD j false := by
    by_cases hlt : j < l.length
    · exact List.getD_append _ _ _ _ hlt
    · rw [List.getD_eq_default (l ++ [a]) false (n := j) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
          List.getD_eq_default l false (n := j) (by omega)]
  have run_len (gs : List Gate) (ws : List Bool) : (run gs ws).length = ws.length + gs.length := by
    induction gs generalizing ws with
    | nil => simp only [run, List.foldl_nil, List.length_nil, Nat.add_zero]
    | cons g rest ih =>
      simp only [run, List.foldl_cons] at ih ⊢
      rw [ih (step ws g)]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
  have run_append (gs1 gs2 : List Gate) (ws : List Bool) :
      run (gs1 ++ gs2) ws = run gs2 (run gs1 ws) := by
    simp only [run, List.foldl_append]
  have run_keep (gs : List Gate) (ws : List Bool) :
      ∀ i < ws.length, (run gs ws).getD i false = ws.getD i false := by
    induction gs generalizing ws with
    | nil => intro i _; rfl
    | cons g rest ih =>
      intro i hi
      simp only [run, List.foldl_cons] at ih ⊢
      have hi' : i < (step ws g).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
      rw [ih (step ws g) i hi']
      exact List.getD_append _ _ _ _ hi
  let rd : (C : Circuit) → Fin 9 → Finset (Fin C.size) := fun C v =>
    Finset.univ.filter (fun i : Fin C.size => v.val ∈ (C.gates.get i).inputs)
  let Good : Circuit → Prop := fun C =>
    IsMinimalCircuit 9 C ∧ C.size ≤ 15 ∧ circuitFun 9 C = p9 ∧
    (∀ i : Fin C.size,
      (∀ u ∈ (C.gates.get i).inputs, u < 9 + i.val) ∧ (C.gates.get i).inputs.Nodup ∧
      ((C.gates.get i).op = GateOp.not ∧ (C.gates.get i).inputs.length = 1 ∨
        (C.gates.get i).op ≠ GateOp.not ∧ (C.gates.get i).inputs.length = 2)) ∧
    ∀ v ∈ ([4, 6, 7] : List (Fin 9)),
      (rd C v).Nonempty ∧ (rd C v).card ≤ 2 ∧
      ((rd C v).card = 2 → ∀ i ∈ rd C v, (C.gates.get i).op = GateOp.or)
  have hGood0 : Good C0 := by
    obtain ⟨hmin, hsz, hfun, hnorm, h467⟩ := h30
    rw [hp9_x1] at hfun
    exact ⟨hmin, hsz, hfun, hnorm, h467⟩
  have hRelabel (π πInv : Fin 9 → Fin 9) (h1 : ∀ i, π (πInv i) = i) (h2 : ∀ i, πInv (π i) = i)
      (hp9p : ∀ x : Fin 9 → Bool, p9 (fun i => x (π i)) = p9 x)
      (h467inv : ∀ u : Fin 9, u ∈ ([4, 6, 7] : List (Fin 9)) → πInv u ∈ ([4, 6, 7] : List (Fin 9)))
      (C : Circuit) (hG : Good C) (v : Fin 9) (j0 : Fin C.size)
      (hj0_in : v.val ∈ (C.gates.get j0).inputs) (hj0_ne : (C.gates.get j0).op ≠ GateOp.or) :
      ∃ C' : Circuit, Good C' ∧ ∃ j' : Fin C'.size, (π v).val ∈ (C'.gates.get j').inputs ∧ (C'.gates.get j').op ≠ GateOp.or := by
    let mw : ℕ → ℕ := fun i => if h : i < 9 then (π ⟨i, h⟩).val else i
    have hmw_inj : Function.Injective mw := by
      intro a b hab
      by_cases ha : a < 9
      · by_cases hb : b < 9
        · simp only [mw, ha, hb, ↓reduceDIte] at hab
          have hpi : π ⟨a, ha⟩ = π ⟨b, hb⟩ := Fin.ext hab
          have hfin : (⟨a, ha⟩ : Fin 9) = ⟨b, hb⟩ := by rw [← h2 ⟨a, ha⟩, ← h2 ⟨b, hb⟩, hpi]
          exact congrArg Fin.val hfin
        · simp only [mw, ha, hb, ↓reduceDIte] at hab
          have := (π ⟨a, ha⟩).isLt
          omega
      · by_cases hb : b < 9
        · simp only [mw, ha, hb, ↓reduceDIte] at hab
          have := (π ⟨b, hb⟩).isLt
          omega
        · simp only [mw, ha, hb, ↓reduceDIte] at hab
          exact hab
    let C' : Circuit := ⟨C.gates.map fun g => ⟨g.op, g.inputs.map mw⟩, mw C.output⟩
    have hsz_eq : C'.size = C.size := List.length_map _
    have hget (i : Fin C'.size) :
        C'.gates.get i = ⟨(C.gates.get (i.cast hsz_eq)).op, (C.gates.get (i.cast hsz_eq)).inputs.map mw⟩ := by
      change (C.gates.map fun g : Gate => Gate.mk g.op (g.inputs.map mw))[i.val]'(by rw [List.length_map]; exact (i.cast hsz_eq).isLt) = _
      rw [List.getElem_map]
      rfl
    have hsim (gs : List Gate) (wA wB : List Bool) (hlen : wA.length = wB.length) (h9 : 9 ≤ wA.length)
        (hrel : ∀ i, wA.getD (mw i) false = wB.getD i false) :
        ∀ i, (run (gs.map fun g => ⟨g.op, g.inputs.map mw⟩) wA).getD (mw i) false = (run gs wB).getD i false := by
      induction gs generalizing wA wB with
      | nil => exact hrel
      | cons g rest ih =>
        simp only [List.map_cons, run, List.foldl_cons] at ih ⊢
        have hinp : (g.inputs.map mw).map (fun j => wA.getD j false) = g.inputs.map (fun i => wB.getD i false) := by
          rw [List.map_map]
          apply List.map_congr_left
          intro i _
          exact hrel i
        let b := g.op.eval (g.inputs.map fun i => wB.getD i false)
        have hstepA : step wA ⟨g.op, g.inputs.map mw⟩ = wA ++ [b] := by
          dsimp only [step, b]; rw [hinp]
        rw [hstepA]
        apply ih (wA ++ [b]) (step wB g)
        · simp only [step, List.length_append, List.length_cons, List.length_nil, hlen]
        · simp only [List.length_append, List.length_cons, List.length_nil]; omega
        · intro i
          dsimp only [step]
          by_cases heq : i = wB.length
          · subst heq
            have hnot9 : ¬ (wB.length < 9) := by omega
            have hmw_len : mw wB.length = wA.length := by simp only [mw, hnot9, ↓reduceDIte, hlen]
            rw [hmw_len, getD_snoc_eq wA b, getD_snoc_eq wB b]
          · have hmw_ne : mw i ≠ wA.length := by
              intro h
              have hnot9 : ¬ (wB.length < 9) := by omega
              have hmw_len : mw wB.length = wA.length := by simp only [mw, hnot9, ↓reduceDIte, hlen]
              exact heq (hmw_inj (h.trans hmw_len.symm))
            rw [getD_snoc_ne wA b (mw i) hmw_ne, getD_snoc_ne wB b i heq]
            exact hrel i
    have hfun' : circuitFun 9 C' = p9 := by
      funext x
      have hbase : ∀ i, (List.ofFn x).getD (mw i) false = (List.ofFn fun k : Fin 9 => x (π k)).getD i false := by
        intro i
        by_cases hi : i < 9
        · simp only [mw, hi, ↓reduceDIte]
          have hlt1 : (π ⟨i, hi⟩).val < (List.ofFn x).length := by simp only [List.length_ofFn]; exact (π ⟨i, hi⟩).isLt
          have hlt2 : i < (List.ofFn fun k : Fin 9 => x (π k)).length := by simp only [List.length_ofFn]; exact hi
          rw [List.getD_eq_getElem _ _ hlt1, List.getElem_ofFn, List.getD_eq_getElem _ _ hlt2, List.getElem_ofFn]
        · simp only [mw, hi, ↓reduceDIte]
          rw [List.getD_eq_default (List.ofFn x) false (n := i) (by simp only [List.length_ofFn]; omega),
              List.getD_eq_default (List.ofFn fun k : Fin 9 => x (π k)) false (n := i) (by simp only [List.length_ofFn]; omega)]
      have hev := hsim C.gates (List.ofFn x) (List.ofFn fun k : Fin 9 => x (π k))
        (by simp only [List.length_ofFn]) (by simp only [List.length_ofFn]; omega) hbase C.output
      change (run C'.gates (List.ofFn x)).getD (mw C.output) false = p9 x
      rw [hev]
      have hCeq : (run C.gates (List.ofFn fun k : Fin 9 => x (π k))).getD C.output false = p9 (fun k => x (π k)) :=
        congrFun hG.2.2.1 (fun k => x (π k))
      rw [hCeq, hp9p x]
    have hfan' : FanInTwo C' := by
      intro g hg
      simp only [C', List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      have hf := hG.1.1 g0 hg0
      exact ⟨hf.1, by simp only [List.length_map]; exact hf.2⟩
    have hmin' : IsMinimalCircuit 9 C' :=
      ⟨hfan', fun D hDF hDeq => by
        rw [hsz_eq]
        exact hG.1.2 D hDF (hDeq.trans (hfun'.trans hG.2.2.1.symm))⟩
    have hnorm' : ∀ i : Fin C'.size,
        (∀ u ∈ (C'.gates.get i).inputs, u < 9 + i.val) ∧ (C'.gates.get i).inputs.Nodup ∧
        ((C'.gates.get i).op = GateOp.not ∧ (C'.gates.get i).inputs.length = 1 ∨
          (C'.gates.get i).op ≠ GateOp.not ∧ (C'.gates.get i).inputs.length = 2) := by
      intro i
      rw [hget i]
      have hn := hG.2.2.2.1 (i.cast hsz_eq)
      refine ⟨?_, List.Nodup.map hmw_inj hn.2.1, ?_⟩
      · intro u hu
        rw [List.mem_map] at hu
        obtain ⟨u0, hu0, rfl⟩ := hu
        have hlt := hn.1 u0 hu0
        by_cases h9 : u0 < 9
        · simp only [mw, h9, ↓reduceDIte]
          have := (π ⟨u0, h9⟩).isLt
          omega
        · simp only [mw, h9, ↓reduceDIte]
          simp only [Fin.val_cast] at hlt
          omega
      · simp only [List.length_map]
        exact hn.2.2
    have hmem_iff (u : Fin 9) (i : Fin C'.size) :
        u.val ∈ (C'.gates.get i).inputs ↔ (πInv u).val ∈ (C.gates.get (i.cast hsz_eq)).inputs := by
      rw [hget i]
      simp only [List.mem_map]
      constructor
      · rintro ⟨w0, hw0, hmw⟩
        have hpi : mw (πInv u).val = u.val := by
          simp only [mw, (πInv u).isLt, ↓reduceDIte, Fin.eta, h1 u]
        have heq : w0 = (πInv u).val := hmw_inj (hmw.trans hpi.symm)
        rw [← heq]
        exact hw0
      · intro h
        exact ⟨(πInv u).val, h, by simp only [mw, (πInv u).isLt, ↓reduceDIte, Fin.eta, h1 u]⟩
    have h467' : ∀ u ∈ ([4, 6, 7] : List (Fin 9)),
        (rd C' u).Nonempty ∧ (rd C' u).card ≤ 2 ∧
        ((rd C' u).card = 2 → ∀ i ∈ rd C' u, (C'.gates.get i).op = GateOp.or) := by
      intro u hu
      have horig := hG.2.2.2.2 (πInv u) (h467inv u hu)
      have hbi : rd C' u = (rd C (πInv u)).image (fun k : Fin C.size => k.cast hsz_eq.symm) := by
        ext i
        simp only [rd, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        rw [hmem_iff u i]
        constructor
        · intro h
          exact ⟨i.cast hsz_eq, h, Fin.ext rfl⟩
        · rintro ⟨k, hk, rfl⟩
          exact hk
      have hcard_eq : (rd C' u).card = (rd C (πInv u)).card := by
        rw [hbi]
        exact Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa only [Fin.val_cast] using congrArg Fin.val h))
      refine ⟨?_, by omega, ?_⟩
      · obtain ⟨k, hk⟩ := horig.1
        exact ⟨k.cast hsz_eq.symm, by rw [hbi]; exact Finset.mem_image_of_mem _ hk⟩
      · intro hcard2 i hi
        rw [hbi, Finset.mem_image] at hi
        obtain ⟨k, hk, rfl⟩ := hi
        rw [hget (k.cast hsz_eq.symm)]
        exact horig.2.2 (by omega) k hk
    refine ⟨C', ⟨hmin', by omega, hfun', hnorm', h467'⟩, j0.cast hsz_eq.symm, ?_, ?_⟩
    · rw [hmem_iff (π v) (j0.cast hsz_eq.symm), h2 v]
      exact hj0_in
    · rw [hget (j0.cast hsz_eq.symm)]
      exact hj0_ne
  have hWLOG4 : ∃ C : Circuit, Good C ∧ ∃ j : Fin C.size, 4 ∈ (C.gates.get j).inputs ∧ (C.gates.get j).op ≠ GateOp.or := by
    obtain ⟨v, hv, j0, hj0_mem, hj0_ne⟩ := hex0
    have hj0_in : v.val ∈ (C0.gates.get j0).inputs := (Finset.mem_filter.mp hj0_mem).2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact ⟨C0, hGood0, j0, hj0_in, hj0_ne⟩
    · obtain ⟨C', hG', j', hj'in, hj'ne⟩ := hRelabel τ σ hτσ hστ
        (hp9_perm τ σ hτσ hστ hτ_adj hσ_adj) hσ467 C0 hGood0 6 j0 hj0_in hj0_ne
      rw [hτ6] at hj'in
      exact ⟨C', hG', j', hj'in, hj'ne⟩
    · obtain ⟨C', hG', j', hj'in, hj'ne⟩ := hRelabel σ τ hστ hτσ
        (hp9_perm σ τ hστ hτσ hσ_adj hτ_adj) hτ467 C0 hGood0 7 j0 hj0_in hj0_ne
      rw [hσ7] at hj'in
      exact ⟨C', hG', j', hj'in, hj'ne⟩
  obtain ⟨C, hGood, j, hj_in, hj_ne_or⟩ := hWLOG4
  obtain ⟨hMin, hSz15, hFun, hNorm, h467⟩ := hGood
  have hCsz_def : C.gates.length = C.size := rfl
  have h4_bounds := h467 4 (by simp only [List.mem_cons, true_or])
  have hj_mem_rd : j ∈ rd C 4 := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj_in⟩
  have h4_card_ne2 : (rd C 4).card ≠ 2 := fun h2 => hj_ne_or (h4_bounds.2.2 h2 j hj_mem_rd)
  have h4_card_le1 : (rd C 4).card ≤ 1 := by omega
  have h4_uniq : ∀ i : Fin C.size, 4 ∈ (C.gates.get i).inputs ↔ i = j := by
    intro i
    constructor
    · intro hi
      have him : i ∈ rd C 4 := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      exact Finset.card_le_one.mp h4_card_le1 i him j hj_mem_rd
    · rintro rfl; exact hj_in
  have hout_ne4 : C.output ≠ 4 := by
    intro hout4
    let e4 : Fin 9 → Bool := fun i => decide (i = 4)
    have hp9_e4 : p9 e4 = false := by decide
    have hev : circuitFun 9 C e4 = true := by
      change (run C.gates (List.ofFn e4)).getD C.output false = true
      rw [hout4, run_keep C.gates (List.ofFn e4) 4 (by simp only [List.length_ofFn]; omega)]
      have hlt : 4 < (List.ofFn e4).length := by simp only [List.length_ofFn]; omega
      rw [List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
      rfl
    have hfun_e4 : circuitFun 9 C e4 = p9 e4 := congrFun hFun e4
    rw [hev, hp9_e4] at hfun_e4
    cases hfun_e4
  have hno4_prefix : ∀ g ∈ C.gates.take j.val, 4 ∉ g.inputs := by
    intro g hg h4g
    obtain ⟨idx, hidx_lt, rfl⟩ := List.getElem_of_mem hg
    have hidx_j : idx < j.val := by simp only [List.length_take] at hidx_lt; omega
    have hidx_C : idx < C.size := by omega
    rw [List.getElem_take] at h4g
    have heq := (h4_uniq ⟨idx, hidx_C⟩).mp h4g
    have hval := congrArg Fin.val heq
    simp only at hval
    omega
  have hno4_suffix : ∀ g ∈ C.gates.drop (j.val + 1), 4 ∉ g.inputs := by
    intro g hg h4g
    obtain ⟨idx, hidx_lt, rfl⟩ := List.getElem_of_mem hg
    have hidx_C : j.val + 1 + idx < C.size := by simp only [List.length_drop] at hidx_lt; omega
    rw [List.getElem_drop] at h4g
    have heq := (h4_uniq ⟨j.val + 1 + idx, hidx_C⟩).mp h4g
    have hval := congrArg Fin.val heq
    simp only at hval
    omega
  have hsplit_gates : C.gates = C.gates.take j.val ++ [C.gates.get j] ++ C.gates.drop (j.val + 1) := by
    have h2 : C.gates.drop j.val = C.gates.get j :: C.gates.drop (j.val + 1) := by
      change C.gates.drop j.val = C.gates[j.val] :: C.gates.drop (j.val + 1)
      exact List.drop_eq_getElem_cons j.isLt
    calc C.gates = C.gates.take j.val ++ C.gates.drop j.val := (List.take_append_drop j.val C.gates).symm
      _ = C.gates.take j.val ++ (C.gates.get j :: C.gates.drop (j.val + 1)) := by rw [h2]
      _ = C.gates.take j.val ++ [C.gates.get j] ++ C.gates.drop (j.val + 1) := by rw [List.append_assoc, List.singleton_append]
  have hNo4Agree (gs : List Gate) (hno4 : ∀ g ∈ gs, 4 ∉ g.inputs) (wA wB : List Bool)
      (hlen : wA.length = wB.length) (hagree : ∀ i, i ≠ 4 → wA.getD i false = wB.getD i false) :
      (run gs wA).length = (run gs wB).length ∧
      ∀ i, i ≠ 4 → (run gs wA).getD i false = (run gs wB).getD i false := by
    induction gs generalizing wA wB with
    | nil => exact ⟨hlen, hagree⟩
    | cons g rest ih =>
      simp only [run, List.foldl_cons] at ih ⊢
      have hg4 : 4 ∉ g.inputs := hno4 g List.mem_cons_self
      have hinp : g.inputs.map (fun i => wA.getD i false) = g.inputs.map (fun i => wB.getD i false) := by
        apply List.map_congr_left
        intro i hi
        exact hagree i (fun h => hg4 (h ▸ hi))
      apply ih (fun g' hg' => hno4 g' (List.mem_cons_of_mem g hg')) (step wA g) (step wB g)
      · simp only [step, List.length_append, List.length_cons, List.length_nil, hlen]
      · intro i hi4
        dsimp only [step]
        rw [hinp]
        by_cases heq : i = wA.length
        · subst heq
          rw [getD_snoc_eq wA _, hlen, getD_snoc_eq wB _]
        · have heq2 : i ≠ wB.length := by rw [← hlen]; exact heq
          rw [getD_snoc_ne wA _ i heq, getD_snoc_ne wB _ i heq2]
          exact hagree i hi4
  have hj_fan := hMin.1 (C.gates.get j) (List.get_mem C.gates j)
  rcases hj_fan.1 with hand | hor | hnot
  · have hj_norm := hNorm j
    have hj_len2 : (C.gates.get j).inputs.length = 2 := by
      rcases hj_norm.2.2 with ⟨hcon, _⟩ | ⟨_, h2⟩
      · rw [hand] at hcon; cases hcon
      · exact h2
    have hpair : ∃ a b : ℕ, (C.gates.get j).inputs = [a, b] := by
      cases h : (C.gates.get j).inputs with
      | nil => rw [h] at hj_len2; cases hj_len2
      | cons a rest =>
        cases rest with
        | nil => rw [h] at hj_len2; cases hj_len2
        | cons b rest2 =>
          cases rest2 with
          | nil => exact ⟨a, b, rfl⟩
          | cons _ _ => rw [h] at hj_len2; cases hj_len2
    obtain ⟨a, b, hab⟩ := hpair
    have hab_ne : a ≠ b := by
      have hnd := hj_norm.2.1
      rw [hab, List.nodup_cons, List.mem_singleton] at hnd
      exact hnd.1
    have h4ab : a = 4 ∨ b = 4 := by
      have h := hj_in
      rw [hab, List.mem_cons, List.mem_singleton] at h
      rcases h with h1 | h2
      · exact Or.inl h1.symm
      · exact Or.inr h2.symm
    let w : ℕ := if a = 4 then b else a
    have hw_in : w ∈ (C.gates.get j).inputs := by
      rw [hab]
      by_cases ha4 : a = 4
      · simp only [w, ha4, ↓reduceIte]
        exact List.mem_cons_of_mem 4 List.mem_cons_self
      · simp only [w, ha4, ↓reduceIte]
        exact List.mem_cons_self
    have hw_ne4 : w ≠ 4 := by
      by_cases ha4 : a = 4
      · simp only [w, ha4, ↓reduceIte]; intro hb4; exact hab_ne (ha4.trans hb4.symm)
      · simp only [w, ha4, ↓reduceIte]; exact ha4
    have hw_lt : w < 9 + j.val := hj_norm.1 w hw_in
    have hj_eval (ws : List Bool) :
        (C.gates.get j).op.eval ((C.gates.get j).inputs.map fun i => ws.getD i false) =
          (ws.getD 4 false && ws.getD w false) := by
      rw [hand, hab]
      simp only [List.map_cons, List.map_nil, hand_eval]
      by_cases ha4 : a = 4
      · simp only [w, ha4, ↓reduceIte]
      · have hb4 : b = 4 := by rcases h4ab with h | h; exact absurd h ha4; exact h
        simp only [w, ha4, hb4, ↓reduceIte, Bool.and_comm]
    have hForce : ∀ x : Fin 9 → Bool, x 4 = false → p9 x = false → (x 0 = true ∨ x 3 = true) →
        (C.wires (List.ofFn x)).getD w false = true := by
      intro x hx4 hpx h03
      cases hwv : (C.wires (List.ofFn x)).getD w false
      · exfalso
        let x' : Fin 9 → Bool := Function.update x 4 true
        have hp9_x' : p9 x' = true := by
          simp only [p9, decide_eq_true_eq]
          have h04 : (mask.getD (0 : Fin 9).val 0).testBit (4 : Fin 9).val = true := by decide
          have h34 : (mask.getD (3 : Fin 9).val 0).testBit (4 : Fin 9).val = true := by decide
          have hx'4 : x' 4 = true := Function.update_self 4 true x
          rcases h03 with h0 | h3
          · refine ⟨0, 4, h04, ?_, hx'4⟩
            dsimp only [x']; rw [Function.update_of_ne (by decide)]; exact h0
          · refine ⟨3, 4, h34, ?_, hx'4⟩
            dsimp only [x']; rw [Function.update_of_ne (by decide)]; exact h3
        have hbase_ag : ∀ i, i ≠ 4 → (List.ofFn x).getD i false = (List.ofFn x').getD i false := by
          intro i hi4
          by_cases hi : i < 9
          · have hlt1 : i < (List.ofFn x).length := by simp only [List.length_ofFn]; exact hi
            have hlt2 : i < (List.ofFn x').length := by simp only [List.length_ofFn]; exact hi
            rw [List.getD_eq_getElem _ _ hlt1, List.getElem_ofFn, List.getD_eq_getElem _ _ hlt2, List.getElem_ofFn]
            dsimp only [x']
            rw [Function.update_of_ne (fun h => hi4 (congrArg Fin.val h))]
          · rw [List.getD_eq_default (List.ofFn x) false (n := i) (by simp only [List.length_ofFn]; omega),
                List.getD_eq_default (List.ofFn x') false (n := i) (by simp only [List.length_ofFn]; omega)]
        let wA1 := run (C.gates.take j.val) (List.ofFn x)
        let wB1 := run (C.gates.take j.val) (List.ofFn x')
        have h1_ag := hNo4Agree (C.gates.take j.val) hno4_prefix (List.ofFn x) (List.ofFn x')
          (by simp only [List.length_ofFn]) hbase_ag
        have hwA1_len : wA1.length = 9 + j.val := by
          dsimp only [wA1]; rw [run_len, List.length_ofFn, List.length_take]; omega
        have hwA1_w : wA1.getD w false = false := by
          have hkeep : (run C.gates (List.ofFn x)).getD w false = wA1.getD w false := by
            conv_lhs => rw [hsplit_gates, run_append, run_append]
            have hrun2 : run (C.gates.drop (j.val + 1)) (run [C.gates.get j] wA1) =
                run ([C.gates.get j] ++ C.gates.drop (j.val + 1)) wA1 := (run_append _ _ _).symm
            rw [hrun2]
            exact run_keep _ wA1 w (by rw [hwA1_len]; exact hw_lt)
          rw [← hkeep]
          exact hwv
        have hwB1_w : wB1.getD w false = false := by
          rw [← h1_ag.2 w hw_ne4]
          exact hwA1_w
        have hstep_ag : ∀ i, i ≠ 4 → (step wA1 (C.gates.get j)).getD i false = (step wB1 (C.gates.get j)).getD i false := by
          intro i hi4
          have hbA : (C.gates.get j).op.eval ((C.gates.get j).inputs.map fun k => wA1.getD k false) = false := by
            rw [hj_eval wA1, hwA1_w, Bool.and_false]
          have hbB : (C.gates.get j).op.eval ((C.gates.get j).inputs.map fun k => wB1.getD k false) = false := by
            rw [hj_eval wB1, hwB1_w, Bool.and_false]
          dsimp only [step]
          rw [hbA, hbB]
          by_cases heq : i = wA1.length
          · subst heq
            rw [getD_snoc_eq wA1 false, h1_ag.1, getD_snoc_eq wB1 false]
          · have heq2 : i ≠ wB1.length := by rw [← h1_ag.1]; exact heq
            rw [getD_snoc_ne wA1 false i heq, getD_snoc_ne wB1 false i heq2]
            exact h1_ag.2 i hi4
        have h2_ag := hNo4Agree (C.gates.drop (j.val + 1)) hno4_suffix (step wA1 (C.gates.get j)) (step wB1 (C.gates.get j))
          (by dsimp only [wA1, wB1]; simp only [step, List.length_append, List.length_cons, List.length_nil, h1_ag.1]) hstep_ag
        have hev_eq : circuitFun 9 C x = circuitFun 9 C x' := by
          change (run C.gates (List.ofFn x)).getD C.output false = (run C.gates (List.ofFn x')).getD C.output false
          conv_lhs => rw [hsplit_gates, run_append, run_append]
          conv_rhs => rw [hsplit_gates, run_append, run_append]
          exact h2_ag.2 C.output hout_ne4
        have hfx : circuitFun 9 C x = p9 x := congrFun hFun x
        have hfx' : circuitFun 9 C x' = p9 x' := congrFun hFun x'
        rw [hfx, hfx', hpx, hp9_x'] at hev_eq
        cases hev_eq
      · rfl
    have hw_ge9 : 9 ≤ w := by
      by_contra hlt9
      have hw9 : w < 9 := by omega
      let e0 : Fin 9 → Bool := fun i => decide (i = 0)
      let e3 : Fin 9 → Bool := fun i => decide (i = 3)
      have h0_true : (C.wires (List.ofFn e0)).getD w false = true :=
        hForce e0 (by decide) (by decide) (Or.inl (by decide))
      have h3_true : (C.wires (List.ofFn e3)).getD w false = true :=
        hForce e3 (by decide) (by decide) (Or.inr (by decide))
      have hget_w (e : Fin 9 → Bool) : (C.wires (List.ofFn e)).getD w false = e ⟨w, hw9⟩ := by
        change (run C.gates (List.ofFn e)).getD w false = e ⟨w, hw9⟩
        have hlt : w < (List.ofFn e).length := by simp only [List.length_ofFn]; exact hw9
        rw [run_keep C.gates (List.ofFn e) w hlt, List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
      rw [hget_w e0] at h0_true
      rw [hget_w e3] at h3_true
      have hw0 : (⟨w, hw9⟩ : Fin 9) = 0 := by simpa only [e0, decide_eq_true_eq] using h0_true
      have hw3 : (⟨w, hw9⟩ : Fin 9) = 3 := by simpa only [e3, decide_eq_true_eq] using h3_true
      have h03 : (0 : Fin 9) = 3 := hw0.symm.trans hw3
      cases h03
    let k : Fin C.size := ⟨w - 9, by omega⟩
    have hkj : k < j := by change w - 9 < j.val; omega
    have h9k : 9 + k.val = w := by change 9 + (w - 9) = w; omega
    rw [← h9k] at hw_in hForce
    have hk_fan := hMin.1 (C.gates.get k) (List.get_mem C.gates k)
    rcases hk_fan.1 with hk_and | hk_or | hk_not
    · exact hSoleAndFromAnd C hMin hSz15 hFun hNorm h467 ⟨j, k, hkj, h4_uniq, hand, hw_in, hk_and, hForce⟩
    · exact hSoleAndFromOr C hMin hSz15 hFun hNorm h467 ⟨j, k, hkj, h4_uniq, hand, hw_in, hk_or, hForce⟩
    · exact hSoleAndFromNot C hMin hSz15 hFun hNorm h467 ⟨j, k, hkj, h4_uniq, hand, hw_in, hk_not, hForce⟩
  · exact absurd hor hj_ne_or
  · have hj_norm := hNorm j
    have hj_len1 : (C.gates.get j).inputs.length = 1 := by
      rcases hj_norm.2.2 with ⟨_, h1⟩ | ⟨hcon, _⟩
      · exact h1
      · exact absurd hnot hcon
    have hj_inp4 : (C.gates.get j).inputs = [4] := by
      cases h : (C.gates.get j).inputs with
      | nil => rw [h] at hj_len1; cases hj_len1
      | cons a rest =>
        cases rest with
        | nil =>
          have h4 := hj_in
          rw [h, List.mem_singleton] at h4
          subst h4
          rfl
        | cons _ _ => rw [h] at hj_len1; cases hj_len1
    let redir : ℕ → ℕ := fun i => if i = 9 + j.val then 4 else if 9 + j.val < i then i - 1 else i
    let D : Circuit := ⟨C.gates.take j.val ++ (C.gates.drop (j.val + 1)).map (fun g => ⟨g.op, g.inputs.map redir⟩), redir C.output⟩
    have hD_fan : FanInTwo D := by
      intro g hg
      simp only [D, List.mem_append, List.mem_map] at hg
      rcases hg with hg1 | ⟨g0, hg0, rfl⟩
      · exact hMin.1 g (List.mem_of_mem_take hg1)
      · have hf := hMin.1 g0 (List.mem_of_mem_drop hg0)
        exact ⟨hf.1, by simp only [List.length_map]; exact hf.2⟩
    have hD_sz : D.size ≤ 14 := by
      change (C.gates.take j.val ++ (C.gates.drop (j.val + 1)).map _).length ≤ 14
      simp only [List.length_append, List.length_take, List.length_map, List.length_drop]
      have hjlt : j.val < C.gates.length := j.isLt
      have hlen15 : C.gates.length ≤ 15 := hSz15
      omega
    have hD_sim : ∀ y : Fin 9 → Bool, D.eval (List.ofFn y) = p9 (Function.update y 4 (!y 4)) := by
      intro y
      let x : Fin 9 → Bool := Function.update y 4 (!y 4)
      have hbase_ag : ∀ i, i ≠ 4 → (List.ofFn y).getD i false = (List.ofFn x).getD i false := by
        intro i hi4
        by_cases hi : i < 9
        · have hlt1 : i < (List.ofFn y).length := by simp only [List.length_ofFn]; exact hi
          have hlt2 : i < (List.ofFn x).length := by simp only [List.length_ofFn]; exact hi
          rw [List.getD_eq_getElem _ _ hlt1, List.getElem_ofFn, List.getD_eq_getElem _ _ hlt2, List.getElem_ofFn]
          dsimp only [x]
          rw [Function.update_of_ne (fun h => hi4 (congrArg Fin.val h))]
        · rw [List.getD_eq_default (List.ofFn y) false (n := i) (by simp only [List.length_ofFn]; omega),
              List.getD_eq_default (List.ofFn x) false (n := i) (by simp only [List.length_ofFn]; omega)]
      let wA1 := run (C.gates.take j.val) (List.ofFn y)
      let wB1 := run (C.gates.take j.val) (List.ofFn x)
      have h1_ag := hNo4Agree (C.gates.take j.val) hno4_prefix (List.ofFn y) (List.ofFn x)
        (by simp only [List.length_ofFn]) hbase_ag
      have hwA1_len : wA1.length = 9 + j.val := by
        dsimp only [wA1]; rw [run_len, List.length_ofFn, List.length_take]; omega
      have hwB1_len : wB1.length = 9 + j.val := by rw [← h1_ag.1, hwA1_len]
      let wB2 := step wB1 (C.gates.get j)
      have hmid_rel : ∀ i, i ≠ 4 → wA1.getD (redir i) false = wB2.getD i false := by
        intro i hi4
        by_cases heq : i = 9 + j.val
        · subst heq
          have hred : redir (9 + j.val) = 4 := by simp only [redir, ↓reduceIte]
          rw [hred]
          have hA4 : wA1.getD 4 false = y 4 := by
            dsimp only [wA1]
            have hlt : 4 < (List.ofFn y).length := by simp only [List.length_ofFn]; omega
            rw [run_keep _ _ 4 hlt, List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
            rfl
          have hB4 : wB1.getD 4 false = !y 4 := by
            dsimp only [wB1]
            have hlt : 4 < (List.ofFn x).length := by simp only [List.length_ofFn]; omega
            rw [run_keep _ _ 4 hlt, List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
            exact Function.update_self 4 (!y 4) y
          have hB2_new : wB2.getD (9 + j.val) false = y 4 := by
            dsimp only [wB2, step]
            rw [← hwB1_len, getD_snoc_eq wB1 _, hnot, hj_inp4]
            change (!wB1.getD 4 false) = y 4
            rw [hB4, Bool.not_not]
          rw [hA4, hB2_new]
        · by_cases hgt : 9 + j.val < i
          · have hred : redir i = i - 1 := by simp only [redir, heq, hgt, ↓reduceIte]
            rw [hred,
                List.getD_eq_default wA1 false (n := i - 1) (by omega),
                List.getD_eq_default wB2 false (n := i) (by simp only [wB2, step, List.length_append, List.length_cons, List.length_nil]; omega)]
          · have hred : redir i = i := by simp only [redir, heq, hgt, ↓reduceIte]
            rw [hred]
            dsimp only [wB2, step]
            rw [getD_snoc_ne wB1 _ i (by omega)]
            exact h1_ag.2 i hi4
      have hred_sim (gs : List Gate) (hno4 : ∀ g ∈ gs, 4 ∉ g.inputs)
          (wA wB : List Bool) (hwA : 9 + j.val ≤ wA.length) (hwB : wB.length = wA.length + 1)
          (hrel : ∀ i, i ≠ 4 → wA.getD (redir i) false = wB.getD i false) :
          ∀ i, i ≠ 4 → (run (gs.map fun g => ⟨g.op, g.inputs.map redir⟩) wA).getD (redir i) false =
            (run gs wB).getD i false := by
        induction gs generalizing wA wB with
        | nil => exact hrel
        | cons g rest ih =>
          simp only [List.map_cons, run, List.foldl_cons] at ih ⊢
          have hg4 : 4 ∉ g.inputs := hno4 g List.mem_cons_self
          have hinp : (g.inputs.map redir).map (fun k => wA.getD k false) = g.inputs.map (fun i => wB.getD i false) := by
            rw [List.map_map]
            apply List.map_congr_left
            intro i hi
            exact hrel i (fun h => hg4 (h ▸ hi))
          let b := g.op.eval (g.inputs.map fun i => wB.getD i false)
          have hstepA : step wA ⟨g.op, g.inputs.map redir⟩ = wA ++ [b] := by
            dsimp only [step, b]; rw [hinp]
          rw [hstepA]
          apply ih (fun g' hg' => hno4 g' (List.mem_cons_of_mem g hg')) (wA ++ [b]) (step wB g)
          · simp only [List.length_append, List.length_cons, List.length_nil]; omega
          · simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
          · intro i hi4
            dsimp only [step]
            by_cases heq : i = wB.length
            · subst heq
              have hne_j : wB.length ≠ 9 + j.val := by omega
              have hgt_j : 9 + j.val < wB.length := by omega
              have hred : redir wB.length = wA.length := by simp only [redir, hne_j, hgt_j, ↓reduceIte]; omega
              rw [hred, getD_snoc_eq wA b, getD_snoc_eq wB b]
            · have hred_ne : redir i ≠ wA.length := by
                dsimp only [redir]
                by_cases h1 : i = 9 + j.val
                · simp only [h1, ↓reduceIte]; omega
                · by_cases h2 : 9 + j.val < i
                  · simp only [h1, h2, ↓reduceIte]; omega
                  · simp only [h1, h2, ↓reduceIte]; omega
              rw [getD_snoc_ne wA b (redir i) hred_ne, getD_snoc_ne wB b i heq]
              exact hrel i hi4
      have hfinal := hred_sim (C.gates.drop (j.val + 1)) hno4_suffix wA1 wB2
        (by omega) (by simp only [wB2, step, List.length_append, List.length_cons, List.length_nil]; omega)
        hmid_rel C.output hout_ne4
      change (run (C.gates.take j.val ++ (C.gates.drop (j.val + 1)).map fun g => ⟨g.op, g.inputs.map redir⟩) (List.ofFn y)).getD (redir C.output) false = p9 x
      rw [run_append, hfinal]
      have hC_eval : (run (C.gates.drop (j.val + 1)) wB2).getD C.output false = circuitFun 9 C x := by
        change _ = (run C.gates (List.ofFn x)).getD C.output false
        conv_rhs => rw [hsplit_gates, run_append, run_append]
        rfl
      rw [hC_eval]
      exact congrFun hFun x
    exact hSoleNot D hD_fan hD_sz hD_sim
