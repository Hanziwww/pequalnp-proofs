import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_5210_17
    (hLe63Unit :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        let S : Finset (Fin 13) := {0, 1, 3, 9}
        let gv : ℕ → (Fin 26 → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal 26 C
        let ic : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone 26 C
        let op : ℕ → ℕ → Prop := PEqualNP.ReadTwo.orp C 26
        let pi : Fin 26 → Fin 26 → Fin 26 → Bool := PEqualNP.EdgeOwnership.pairInput
        let live : ℕ → Prop := fun k =>
          PEqualNP.ReadTwo.isAnd C k ∧ (26 + k = C.output ∨ ic k (C.output - 26)) ∧ gv k (pi 0 13) = true
        let opF : ℕ → (Fin 26 → Bool) → Prop := fun k x =>
          ∀ u : Fin 2, PEqualNP.CleanedNonEdge.wireVal 26 C (PEqualNP.TopForm.opnd C k u) x = false
        C.size ≤ 63 →
        PEqualNP.TopForm.IsAO2 26 C →
        (∀ g ∈ C.gates, g.inputs.Nodup) →
        (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ p l : Fin 13, p - l ∈ S ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
        (∃ p l : Fin 13, p - l ∈ S ∧ ¬ ∃ k u v : ℕ,
          PEqualNP.ReadTwo.andOn C k u v ∧ op (26 + k) C.output ∧ op p.val u ∧ op (13 + l.val) v) →
        ∀ a i j : ℕ,
          a ≠ i → a ≠ j → i ≠ j → ¬ ic i j → ¬ ic j i →
          live a → live i → live j →
          gv a (pi 0 0) = false → gv a (pi 13 13) = false → gv i (pi 13 13) = true →
          opF i (pi 0 0) → opF j (pi 13 13) → False)
    (hEq64Unit :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        let S : Finset (Fin 13) := {0, 1, 3, 9}
        let gv : ℕ → (Fin 26 → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal 26 C
        let ic : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone 26 C
        let op : ℕ → ℕ → Prop := PEqualNP.ReadTwo.orp C 26
        let pi : Fin 26 → Fin 26 → Fin 26 → Bool := PEqualNP.EdgeOwnership.pairInput
        let live : ℕ → Prop := fun k =>
          PEqualNP.ReadTwo.isAnd C k ∧ (26 + k = C.output ∨ ic k (C.output - 26)) ∧ gv k (pi 0 13) = true
        let opF : ℕ → (Fin 26 → Bool) → Prop := fun k x =>
          ∀ u : Fin 2, PEqualNP.CleanedNonEdge.wireVal 26 C (PEqualNP.TopForm.opnd C k u) x = false
        C.size = 64 →
        PEqualNP.TopForm.IsAO2 26 C →
        (∀ g ∈ C.gates, g.inputs.Nodup) →
        (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ p l : Fin 13, p - l ∈ S ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
        (∃ p l : Fin 13, p - l ∈ S ∧ ¬ ∃ k u v : ℕ,
          PEqualNP.ReadTwo.andOn C k u v ∧ op (26 + k) C.output ∧ op p.val u ∧ op (13 + l.val) v) →
        ∀ a i j : ℕ,
          a ≠ i → a ≠ j → i ≠ j → ¬ ic i j → ¬ ic j i →
          live a → live i → live j →
          gv a (pi 0 0) = false → gv a (pi 13 13) = false → gv i (pi 13 13) = true →
          opF i (pi 0 0) → opF j (pi 13 13) → False)
    (hLe63Clean :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        let S : Finset (Fin 13) := {0, 1, 3, 9}
        let gv : ℕ → (Fin 26 → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal 26 C
        let ic : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone 26 C
        let op : ℕ → ℕ → Prop := PEqualNP.ReadTwo.orp C 26
        let isA : ℕ → Prop := PEqualNP.ReadTwo.isAnd C
        let pi : Fin 26 → Fin 26 → Fin 26 → Bool := PEqualNP.EdgeOwnership.pairInput
        let node : ℕ → ℕ → Fin 26 → Fin 26 → Prop := fun a k u v =>
          ic a k ∧ isA a ∧ isA k ∧ (26 + k = C.output ∨ ic k (C.output - 26)) ∧
          gv a (pi 0 13) = true ∧ gv a (pi u u) = false ∧ gv a (pi v v) = false ∧
          gv k (pi 0 13) = true ∧ gv k (pi v v) = false ∧
          ∀ b : Fin 2, PEqualNP.CleanedNonEdge.wireVal 26 C (PEqualNP.TopForm.opnd C k b) (pi u u) = false
        C.size ≤ 63 →
        PEqualNP.TopForm.IsAO2 26 C →
        (∀ g ∈ C.gates, g.inputs.Nodup) →
        (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ p l : Fin 13, p - l ∈ S ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
        (∃ p l : Fin 13, p - l ∈ S ∧ ¬ ∃ k u v : ℕ,
          PEqualNP.ReadTwo.andOn C k u v ∧ op (26 + k) C.output ∧ op p.val u ∧ op (13 + l.val) v) →
        (∃ d : ℕ, isA d ∧ ∃ y : Fin 26 → Bool, gv d y = true ∧ C.eval (List.ofFn y) = false) →
        ∀ a b i j : ℕ, i < j → ¬ ic i j → ¬ ic j i → node a i 0 13 → node b j 13 0 → False)
    (hEq64Clean :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        let S : Finset (Fin 13) := {0, 1, 3, 9}
        let gv : ℕ → (Fin 26 → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal 26 C
        let ic : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone 26 C
        let op : ℕ → ℕ → Prop := PEqualNP.ReadTwo.orp C 26
        let isA : ℕ → Prop := PEqualNP.ReadTwo.isAnd C
        let pi : Fin 26 → Fin 26 → Fin 26 → Bool := PEqualNP.EdgeOwnership.pairInput
        let node : ℕ → ℕ → Fin 26 → Fin 26 → Prop := fun a k u v =>
          ic a k ∧ isA a ∧ isA k ∧ (26 + k = C.output ∨ ic k (C.output - 26)) ∧
          gv a (pi 0 13) = true ∧ gv a (pi u u) = false ∧ gv a (pi v v) = false ∧
          gv k (pi 0 13) = true ∧ gv k (pi v v) = false ∧
          ∀ b : Fin 2, PEqualNP.CleanedNonEdge.wireVal 26 C (PEqualNP.TopForm.opnd C k b) (pi u u) = false
        C.size = 64 →
        PEqualNP.TopForm.IsAO2 26 C →
        (∀ g ∈ C.gates, g.inputs.Nodup) →
        (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ p l : Fin 13, p - l ∈ S ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
        (∃ p l : Fin 13, p - l ∈ S ∧ ¬ ∃ k u v : ℕ,
          PEqualNP.ReadTwo.andOn C k u v ∧ op (26 + k) C.output ∧ op p.val u ∧ op (13 + l.val) v) →
        (∃ d : ℕ, isA d ∧ ∃ y : Fin 26 → Bool, gv d y = true ∧ C.eval (List.ofFn y) = false) →
        ∀ a b i j : ℕ, i < j → ¬ ic i j → ¬ ic j i → node a i 0 13 → node b j 13 0 → False) :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),     have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};     have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and;     have x4 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1;     have x5 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;     have x6 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));     have x7 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x8 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x9 : ℕ → (Fin (26 : ℕ) → Bool) → Prop := fun (x9 : ℕ) (x10 : Fin (26 : ℕ) → Bool) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x9).op = x3 ∧ ((26 : ℕ) + x9 = x1.output ∨ x4 x9 (x1.output - (26 : ℕ))) ∧ x5 x9 x8 = Bool.true ∧ ∀ (x11 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x9 x11) x10 = Bool.false;     x1.size ≤ (64 : ℕ) ∧ (∀ (x10 : ℕ) (x11 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x10]? = Option.some x11 → (x11.op = x3 ∨ x11.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x13 : ℕ) (x14 : ℕ), x11.inputs = [x13, x14] ∧ x13 ≠ x14 ∧ x13 < (26 : ℕ) + x10 ∧ x14 < (26 : ℕ) + x10) ∧ (∀ (x10 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x10) = Bool.true ↔ ∃ (x11 : Fin (13 : ℕ)) (x12 : Fin (13 : ℕ)), x11 - x12 ∈ x2 ∧ x10 (Fin.castAdd (13 : ℕ) x11) = Bool.true ∧ x10 (Fin.natAdd (13 : ℕ) x12) = Bool.true) ∧ (∃ x10 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10).op = x3 ∧ ∃ (x11 : Fin (26 : ℕ) → Bool), x5 x10 x11 = Bool.true ∧ x1.eval (List.ofFn x11) = Bool.false) ∧ ∃ (x10 : ℕ) (x11 : ℕ), x10 ≠ x11 ∧ ¬x4 x10 x11 ∧ ¬x4 x11 x10 ∧ x9 x10 x6 ∧ x9 x11 x7 := by
  let I : Fin 13 → Fin 13 → Prop := fun p l => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
  let e0 : Fin 26 → Bool := PEqualNP.EdgeOwnership.pairInput 0 0
  let e13 : Fin 26 → Bool := PEqualNP.EdgeOwnership.pairInput 13 13
  let e013 : Fin 26 → Bool := PEqualNP.EdgeOwnership.pairInput 0 13
  let dual13 : ℕ → ℕ := fun w =>
    if w < 13 then 13 + (13 - w) % 13 else if w < 26 then (13 - (w - 13)) % 13 else w
  have hdual_lt26_fin : ∀ i : Fin 26, dual13 i.val < 26 := by decide
  have hdual_inv_fin : ∀ i : Fin 26, dual13 (dual13 i.val) = i.val := by decide
  have hdual_ge26 (w : ℕ) (hw : 26 ≤ w) : dual13 w = w := by
    dsimp only [dual13]
    rw [ite_eq_right_iff.mpr (by omega), ite_eq_right_iff.mpr (by omega)]
  have hdual_lt26 (w : ℕ) (hw : w < 26) : dual13 w < 26 := hdual_lt26_fin ⟨w, hw⟩
  have hdual_inv (w : ℕ) : dual13 (dual13 w) = w := by
    by_cases hw : w < 26
    · exact hdual_inv_fin ⟨w, hw⟩
    · rw [hdual_ge26 w (by omega), hdual_ge26 w (by omega)]
  have hdual_inj : Function.Injective dual13 := by
    intro a b h
    rw [← hdual_inv a, ← hdual_inv b, h]
  have hdual_lt_add (k w : ℕ) (hw : w < 26 + k) : dual13 w < 26 + k := by
    by_cases h26 : w < 26
    · have h := hdual_lt26 w h26; omega
    · rw [hdual_ge26 w (by omega)]; exact hw
  let dual13f : Fin 26 → Fin 26 := fun i => ⟨dual13 i.val, hdual_lt26_fin i⟩
  have hdual_cast_val : ∀ p : Fin 13, dual13 (Fin.castAdd 13 p).val = (Fin.natAdd 13 (-p)).val := by decide
  have hdual_nat_val : ∀ l : Fin 13, dual13 (Fin.natAdd 13 l).val = (Fin.castAdd 13 (-l)).val := by decide
  have hdual_cast (p : Fin 13) : dual13f (Fin.castAdd 13 p) = Fin.natAdd 13 (-p) := Fin.ext (hdual_cast_val p)
  have hdual_nat (l : Fin 13) : dual13f (Fin.natAdd 13 l) = Fin.castAdd 13 (-l) := Fin.ext (hdual_nat_val l)
  have hpg_neg : ∀ p l : Fin 13,
      (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ↔
      (-l = -p ∨ -l = -p + 1 ∨ -l = -p + 3 ∨ -l = -p + 9) := by decide
  have hpg_sub_iff : ∀ p l : Fin 13,
      (p - l ∈ ({(0 : Fin 13), 1, 3, 9} : Finset (Fin 13))) ↔
      (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) := by decide
  have hdual_e013_fin : ∀ i : Fin 26, e013 (dual13f i) = e013 i := by
    intro i
    change decide (dual13f i = 0 ∨ dual13f i = 13) = decide (i = 0 ∨ i = 13)
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Fin.ext_iff]
    dsimp only [dual13f, dual13]
    have hi := i.isLt
    split_ifs <;> omega
  have hdual_e0_fin : ∀ i : Fin 26, e0 (dual13f i) = e13 i := by
    intro i
    change decide (dual13f i = 0 ∨ dual13f i = 0) = decide (i = 13 ∨ i = 13)
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Fin.ext_iff]
    dsimp only [dual13f, dual13]
    have hi := i.isLt
    split_ifs <;> omega
  have hdual_e13_fin : ∀ i : Fin 26, e13 (dual13f i) = e0 i := by
    intro i
    change decide (dual13f i = 13 ∨ dual13f i = 13) = decide (i = 0 ∨ i = 0)
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Fin.ext_iff]
    dsimp only [dual13f, dual13]
    have hi := i.isLt
    split_ifs <;> omega
  have hdual_e013 : (fun i : Fin 26 => e013 (dual13f i)) = e013 := funext hdual_e013_fin
  have hdual_e0 : (fun i : Fin 26 => e0 (dual13f i)) = e13 := funext hdual_e0_fin
  have hdual_e13 : (fun i : Fin 26 => e13 (dual13f i)) = e0 := funext hdual_e13_fin
  have he013_true : ∀ i : Fin 26, e013 i = true → i.val = 0 ∨ i.val = 13 := by decide
  have he0_0 : e0 0 = true := by decide
  have he13_13 : e13 13 = true := by decide
  have hdiff_c4 : ∀ a ∈ ([0, 1, 3, 9] : List (Fin 13)), ∀ b ∈ ([0, 1, 3, 9] : List (Fin 13)),
      ∀ c ∈ ([0, 1, 3, 9] : List (Fin 13)), ∀ d ∈ ([0, 1, 3, 9] : List (Fin 13)),
      a ≠ b → a ≠ c → a + d ≠ b + c := by decide
  have hidx4 : ∀ a b : Fin 4, ([0, 1, 3, 9] : List (Fin 13)).getD a.val 0 =
      ([0, 1, 3, 9] : List (Fin 13)).getD b.val 0 → a = b := by decide
  let step : List Bool → Gate → List Bool := fun ws g =>
    ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  let run : List Gate → List Bool → List Bool := fun gs ws => gs.foldl step ws
  have run_len (gs : List Gate) (ws : List Bool) : (run gs ws).length = ws.length + gs.length := by
    induction gs generalizing ws with
    | nil => simp only [run, List.foldl_nil, List.length_nil, Nat.add_zero]
    | cons g rest ih =>
      simp only [run, List.foldl_cons] at ih ⊢
      rw [ih (step ws g)]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
  have getD_snoc_eq {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]
  have getD_snoc_ne {α : Type} (l : List α) (a d : α) (j : ℕ) (hj : j ≠ l.length) :
      (l ++ [a]).getD j d = l.getD j d := by
    by_cases hlt : j < l.length
    · exact List.getD_append _ _ _ _ hlt
    · rw [List.getD_eq_default (l ++ [a]) d (n := j) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
          List.getD_eq_default l d (n := j) (by omega)]
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
  have wireVal_input (D : Circuit) (i : Fin 26) (x : Fin 26 → Bool) :
      wireVal 26 D i.val x = x i := by
    change (run D.gates (List.ofFn x)).getD i.val false = x i
    rw [run_keep D.gates (List.ofFn x) i.val (by simp [i.isLt])]
    rw [List.getD_eq_getElem _ _ (by simp [i.isLt]), List.getElem_ofFn]
  have wireVal_gate (D : Circuit) (hRB : ReadsBack 26 D) (k : ℕ) (hk : k < D.gates.length) (x : Fin 26 → Bool) :
      wireVal 26 D (26 + k) x =
        (gateAt D k).op.eval ((gateAt D k).inputs.map fun i => wireVal 26 D i x) := by
    change (run D.gates (List.ofFn x)).getD (26 + k) false =
      (gateAt D k).op.eval ((gateAt D k).inputs.map fun i => (run D.gates (List.ofFn x)).getD i false)
    have hsplit : D.gates = D.gates.take k ++ [gateAt D k] ++ D.gates.drop (k + 1) := by
      have h1 : D.gates = D.gates.take (k + 1) ++ D.gates.drop (k + 1) :=
        (List.take_append_drop (k + 1) D.gates).symm
      conv_lhs => rw [h1, List.take_succ_eq_append_getElem hk, ← List.getD_eq_getElem D.gates ⟨GateOp.or, []⟩ hk]
      rfl
    let w0 := run (D.gates.take k) (List.ofFn x)
    have hw0_len : w0.length = 26 + k := by
      dsimp only [w0]; rw [run_len, List.length_ofFn, List.length_take]; omega
    have hw_lt : ∀ i < 26 + k, (run D.gates (List.ofFn x)).getD i false = w0.getD i false := by
      intro i hi
      conv_lhs => rw [← List.take_append_drop k D.gates]
      have hfold : run (D.gates.take k ++ D.gates.drop k) (List.ofFn x) = run (D.gates.drop k) w0 := by
        dsimp only [run, w0]; exact List.foldl_append
      rw [hfold]
      exact run_keep (D.gates.drop k) w0 i (by omega)
    have hrun_split : run D.gates (List.ofFn x) = run (D.gates.drop (k + 1)) (step w0 (gateAt D k)) := by
      have h1 : run D.gates (List.ofFn x) = run (D.gates.take k ++ [gateAt D k] ++ D.gates.drop (k + 1)) (List.ofFn x) :=
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
  have wireVal_or_mem (D : Circuit) (hRB : ReadsBack 26 D) {k a : ℕ} (hk : k < D.gates.length)
      (hor : (gateAt D k).op = GateOp.or) (ha : a ∈ (gateAt D k).inputs) (x : Fin 26 → Bool)
      (hva : wireVal 26 D a x = true) : wireVal 26 D (26 + k) x = true := by
    rw [wireVal_gate D hRB k hk x, hor]
    change ((gateAt D k).inputs.map fun i => wireVal 26 D i x).any id = true
    rw [List.any_eq_true]
    exact ⟨true, List.mem_map.mpr ⟨a, ha, hva⟩, rfl⟩
  have wireVal_and_pair (D : Circuit) (hRB : ReadsBack 26 D) {k a b : ℕ} (hk : k < D.gates.length)
      (hand : (gateAt D k).op = GateOp.and) (hin : (gateAt D k).inputs = [a, b]) (x : Fin 26 → Bool) :
      wireVal 26 D (26 + k) x = (wireVal 26 D a x && wireVal 26 D b x) := by
    rw [wireVal_gate D hRB k hk x, hand, hin]
    have h2 : ∀ u v : Bool, GateOp.and.eval [u, v] = (u && v) := by
      intro u v; cases u <;> cases v <;> rfl
    exact h2 _ _
  have wireVal_or_pair (D : Circuit) (hRB : ReadsBack 26 D) {k a b : ℕ} (hk : k < D.gates.length)
      (hor : (gateAt D k).op = GateOp.or) (hin : (gateAt D k).inputs = [a, b]) (x : Fin 26 → Bool) :
      wireVal 26 D (26 + k) x = (wireVal 26 D a x || wireVal 26 D b x) := by
    rw [wireVal_gate D hRB k hk x, hor, hin]
    have h2 : ∀ u v : Bool, GateOp.or.eval [u, v] = (u || v) := by
      intro u v; cases u <;> cases v <;> rfl
    exact h2 _ _
  have isAO2_gate_inputs (D : Circuit) (hAO : IsAO2 26 D) {k : ℕ} (hk : k < D.gates.length) :
      ∃ a b : ℕ, (gateAt D k).inputs = [a, b] ∧ a < 26 + k ∧ b < 26 + k := by
    have hmem : gateAt D k ∈ D.gates := by
      change D.gates.getD k ⟨GateOp.or, []⟩ ∈ D.gates
      rw [List.getD_eq_getElem _ _ hk]
      exact List.getElem_mem hk
    have hlen := hAO.2.2 (gateAt D k) hmem
    cases hin : (gateAt D k).inputs with
    | nil => rw [hin] at hlen; simp at hlen
    | cons a t1 =>
      cases t1 with
      | nil => rw [hin] at hlen; simp at hlen
      | cons b t2 =>
        cases t2 with
        | nil =>
          have ha := hAO.2.1 k hk a (by rw [hin]; exact List.mem_cons_self)
          have hb := hAO.2.1 k hk b (by rw [hin]; exact List.mem_cons_of_mem _ List.mem_cons_self)
          exact ⟨a, b, rfl, ha, hb⟩
        | cons _ _ => rw [hin] at hlen; simp at hlen
  let crun : List Gate → List (List ℕ) → List (List ℕ) := fun gs cs => gs.foldl (coneStep 26) cs
  have crun_len (gs : List Gate) (cs : List (List ℕ)) : (crun gs cs).length = cs.length + gs.length := by
    induction gs generalizing cs with
    | nil => simp only [crun, List.foldl_nil, List.length_nil, Nat.add_zero]
    | cons g rest ih =>
      simp only [crun, List.foldl_cons] at ih ⊢
      rw [ih (coneStep 26 cs g)]
      change (cs ++ [_]).length + rest.length = cs.length + (g :: rest).length
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have crun_keep (gs : List Gate) (cs : List (List ℕ)) :
      ∀ i < cs.length, (crun gs cs).getD i [] = cs.getD i [] := by
    induction gs generalizing cs with
    | nil => intro i _; rfl
    | cons g rest ih =>
      intro i hi
      simp only [crun, List.foldl_cons] at ih ⊢
      have hi' : i < (coneStep 26 cs g).length := by
        change i < (cs ++ [_]).length
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [ih (coneStep 26 cs g) i hi']
      exact List.getD_append _ _ _ _ hi
  have cones_getD_eq (D : Circuit) (k : ℕ) (hk : k < D.gates.length) :
      (cones 26 D).getD k [] =
        ((gateAt D k).inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + k))).flatMap
          (fun w => (w - 26) :: (cones 26 D).getD (w - 26) []) := by
    change (crun D.gates []).getD k [] = _
    have hsplit : D.gates = D.gates.take k ++ [gateAt D k] ++ D.gates.drop (k + 1) := by
      have h1 : D.gates = D.gates.take (k + 1) ++ D.gates.drop (k + 1) :=
        (List.take_append_drop (k + 1) D.gates).symm
      conv_lhs => rw [h1, List.take_succ_eq_append_getElem hk, ← List.getD_eq_getElem D.gates ⟨GateOp.or, []⟩ hk]
      rfl
    let cs0 := crun (D.gates.take k) []
    have hcs0_len : cs0.length = k := by
      dsimp only [cs0]; rw [crun_len, List.length_nil, Nat.zero_add, List.length_take]; omega
    have hcs_lt : ∀ i < k, (crun D.gates []).getD i [] = cs0.getD i [] := by
      intro i hi
      conv_lhs => rw [← List.take_append_drop k D.gates]
      have hfold : crun (D.gates.take k ++ D.gates.drop k) [] = crun (D.gates.drop k) cs0 := by
        dsimp only [crun, cs0]; exact List.foldl_append
      rw [hfold]
      exact crun_keep (D.gates.drop k) cs0 i (by omega)
    have hrun_split : crun D.gates [] = crun (D.gates.drop (k + 1)) (coneStep 26 cs0 (gateAt D k)) := by
      have h1 : crun D.gates [] = crun (D.gates.take k ++ [gateAt D k] ++ D.gates.drop (k + 1)) [] :=
        congrArg (fun gs => crun gs []) hsplit
      rw [h1]
      dsimp only [crun, cs0]
      rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
    conv_lhs => rw [hrun_split]
    rw [crun_keep _ _ k (by
      change k < (cs0 ++ [_]).length
      simp only [List.length_append, hcs0_len, List.length_cons, List.length_nil]; omega)]
    change (cs0 ++ [((gateAt D k).inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs0.length))).flatMap
      (fun w => (w - 26) :: cs0.getD (w - 26) [])]).getD k [] = _
    rw [show k = cs0.length from hcs0_len.symm, getD_snoc_eq cs0 _ []]
    rw [hcs0_len]
    apply List.flatMap_congr
    intro w hw
    have hw_lt : 26 ≤ w ∧ w < 26 + k := by
      have h := (List.mem_filter.mp hw).2
      rwa [decide_eq_true_eq] at h
    change (w - 26) :: cs0.getD (w - 26) [] = (w - 26) :: (crun D.gates []).getD (w - 26) []
    rw [hcs_lt (w - 26) (by omega)]
  have inCone_iff (D : Circuit) (a k : ℕ) (hk : k < D.gates.length) :
      InCone 26 D a k ↔
        ∃ w ∈ (gateAt D k).inputs, 26 ≤ w ∧ w < 26 + k ∧ (a = w - 26 ∨ InCone 26 D a (w - 26)) := by
    change a ∈ (cones 26 D).getD k [] ↔ _
    rw [cones_getD_eq D k hk, List.mem_flatMap]
    constructor
    · rintro ⟨w, hwf, haw⟩
      obtain ⟨hwin, hwb⟩ := List.mem_filter.mp hwf
      rw [decide_eq_true_eq] at hwb
      rcases List.mem_cons.mp haw with rfl | hmem
      · exact ⟨w, hwin, hwb.1, hwb.2, Or.inl rfl⟩
      · exact ⟨w, hwin, hwb.1, hwb.2, Or.inr hmem⟩
    · rintro ⟨w, hwin, hw1, hw2, hdisj⟩
      refine ⟨w, List.mem_filter.mpr ⟨hwin, decide_eq_true ⟨hw1, hw2⟩⟩, ?_⟩
      rcases hdisj with rfl | hmem
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ hmem
  have inCone_lt (D : Circuit) : ∀ k a : ℕ, InCone 26 D a k → a < k ∧ k < D.gates.length := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro a hak
      have hk : k < D.gates.length := by
        by_contra hge
        have hlen : (cones 26 D).length = D.gates.length := by
          change (crun D.gates []).length = D.gates.length
          rw [crun_len, List.length_nil, Nat.zero_add]
        have hempty : (cones 26 D).getD k [] = [] :=
          List.getD_eq_default _ [] (n := k) (by omega)
        change a ∈ (cones 26 D).getD k [] at hak
        rw [hempty] at hak
        cases hak
      refine ⟨?_, hk⟩
      obtain ⟨w, _, hw1, hw2, hdisj⟩ := (inCone_iff D a k hk).mp hak
      rcases hdisj with rfl | hsub
      · omega
      · have hlt := (ih (w - 26) (by omega) a hsub).1
        omega
  have inCone_trans (D : Circuit) : ∀ c a b : ℕ, InCone 26 D a b → InCone 26 D b c → InCone 26 D a c := by
    intro c
    induction c using Nat.strong_induction_on with
    | ind c ih =>
      intro a b hab hbc
      have hc : c < D.gates.length := (inCone_lt D c b hbc).2
      obtain ⟨w, hwin, hw1, hw2, hdisj⟩ := (inCone_iff D b c hc).mp hbc
      rw [inCone_iff D a c hc]
      refine ⟨w, hwin, hw1, hw2, Or.inr ?_⟩
      rcases hdisj with rfl | hsub
      · exact hab
      · exact ih (w - 26) (by omega) a b hab hsub
  let dualGate : Gate → Gate := fun g => ⟨g.op, g.inputs.map dual13⟩
  let dualCirc : Circuit → Circuit := fun D => ⟨D.gates.map dualGate, dual13 D.output⟩
  have filter_dual (l : List ℕ) (m : ℕ) :
      (l.map dual13).filter (fun w => decide (26 ≤ w ∧ w < m)) =
      l.filter (fun w => decide (26 ≤ w ∧ w < m)) := by
    induction l with
    | nil => rfl
    | cons a rest ih =>
      simp only [List.map_cons, List.filter_cons]
      by_cases ha : a < 26
      · have hda : dual13 a < 26 := hdual_lt26 a ha
        have h1 : decide (26 ≤ dual13 a ∧ dual13 a < m) = false := decide_eq_false (by omega)
        have h2 : decide (26 ≤ a ∧ a < m) = false := decide_eq_false (by omega)
        simp only [h1, h2, ih, Bool.false_eq_true, ↓reduceIte]
      · have hda : dual13 a = a := hdual_ge26 a (by omega)
        rw [hda]
        cases decide (26 ≤ a ∧ a < m) <;> simp only [ih]
  have crun_dual (gs : List Gate) (cs : List (List ℕ)) :
      crun (gs.map dualGate) cs = crun gs cs := by
    induction gs generalizing cs with
    | nil => rfl
    | cons g rest ih =>
      simp only [List.map_cons, crun, List.foldl_cons] at ih ⊢
      have hstep : coneStep 26 cs (dualGate g) = coneStep 26 cs g := by
        change cs ++ [((g.inputs.map dual13).filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap _] =
          cs ++ [(g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap _]
        rw [filter_dual]
      rw [hstep]
      exact ih (coneStep 26 cs g)
  have cones_dual (D : Circuit) : cones 26 (dualCirc D) = cones 26 D :=
    crun_dual D.gates []
  have inCone_dual (D : Circuit) (a b : ℕ) : InCone 26 (dualCirc D) a b ↔ InCone 26 D a b := by
    change a ∈ (cones 26 (dualCirc D)).getD b [] ↔ a ∈ (cones 26 D).getD b []
    rw [cones_dual]
  have run_dual (gs : List Gate) (w1 w2 : List Bool) (hlen : w1.length = w2.length) (h26 : 26 ≤ w1.length)
      (hrel : ∀ i, w2.getD i false = w1.getD (dual13 i) false) :
      ∀ i, (run (gs.map dualGate) w2).getD i false = (run gs w1).getD (dual13 i) false := by
    induction gs generalizing w1 w2 with
    | nil => exact hrel
    | cons g rest ih =>
      simp only [List.map_cons, run, List.foldl_cons] at ih ⊢
      have hvals : ((dualGate g).inputs.map fun j => w2.getD j false) =
          (g.inputs.map fun j => w1.getD j false) := by
        dsimp only [dualGate]
        rw [List.map_map]
        apply List.map_congr_left
        intro j _
        dsimp only [Function.comp_apply]
        rw [hrel (dual13 j), hdual_inv j]
      have heval : (dualGate g).op.eval ((dualGate g).inputs.map fun j => w2.getD j false) =
          g.op.eval (g.inputs.map fun j => w1.getD j false) := congrArg g.op.eval hvals
      apply ih (step w1 g) (step w2 (dualGate g))
      · simp only [step, List.length_append, hlen, List.length_cons, List.length_nil]
      · simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
      · intro i
        dsimp only [step]
        rw [heval]
        by_cases hi : i = w1.length
        · subst hi
          have hdl : dual13 w1.length = w1.length := hdual_ge26 w1.length h26
          rw [hdl, getD_snoc_eq w1 _ false, hlen, getD_snoc_eq w2 _ false]
        · have hi2 : i ≠ w2.length := by omega
          have hdi : dual13 i ≠ w1.length := by
            intro heq
            have h1 : i = dual13 w1.length := by rw [← heq, hdual_inv i]
            rw [hdual_ge26 w1.length h26] at h1
            exact hi h1
          rw [getD_snoc_ne w2 _ false i hi2, getD_snoc_ne w1 _ false (dual13 i) hdi]
          exact hrel i
  have wireVal_dual (D : Circuit) (x : Fin 26 → Bool) (w : ℕ) :
      wireVal 26 (dualCirc D) w x = wireVal 26 D (dual13 w) (fun i => x (dual13f i)) := by
    change (run (D.gates.map dualGate) (List.ofFn x)).getD w false =
      (run D.gates (List.ofFn fun i => x (dual13f i))).getD (dual13 w) false
    apply run_dual D.gates (List.ofFn fun i => x (dual13f i)) (List.ofFn x)
      (by simp only [List.length_ofFn]) (by simp only [List.length_ofFn]; omega)
    intro i
    by_cases hi : i < 26
    · have hdi : dual13 i < 26 := hdual_lt26 i hi
      have hi' : i < (List.ofFn x).length := by simp only [List.length_ofFn]; exact hi
      have hdi' : dual13 i < (List.ofFn fun k : Fin 26 => x (dual13f k)).length := by
        simp only [List.length_ofFn]; exact hdi
      rw [List.getD_eq_getElem _ _ hi', List.getElem_ofFn,
        List.getD_eq_getElem _ _ hdi', List.getElem_ofFn]
      congr 1
      apply Fin.ext
      dsimp only [dual13f]
      exact (hdual_inv i).symm
    · have hdi : 26 ≤ dual13 i := by rw [hdual_ge26 i (by omega)]; omega
      rw [List.getD_eq_default (List.ofFn x) false (n := i) (by simp only [List.length_ofFn]; omega),
        List.getD_eq_default (List.ofFn fun k : Fin 26 => x (dual13f k)) false (n := dual13 i)
          (by simp only [List.length_ofFn]; omega)]
  have gateAt_dual (D : Circuit) (k : ℕ) (hk : k < D.gates.length) :
      gateAt (dualCirc D) k = dualGate (gateAt D k) := by
    change (D.gates.map dualGate).getD k ⟨GateOp.or, []⟩ = dualGate (D.gates.getD k ⟨GateOp.or, []⟩)
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_map]; exact hk),
      List.getElem_map, List.getD_eq_getElem _ _ hk]
  have opnd_dual (D : Circuit) (hAO : IsAO2 26 D) (k : ℕ) (hk : k < D.gates.length) (b : Fin 2) :
      opnd (dualCirc D) k b = dual13 (opnd D k b) := by
    obtain ⟨u, v, huv, _, _⟩ := isAO2_gate_inputs D hAO hk
    change ((gateAt (dualCirc D) k).inputs).getD b.val 0 = dual13 (((gateAt D k).inputs).getD b.val 0)
    rw [gateAt_dual D k hk]
    dsimp only [dualGate]
    rw [huv]
    fin_cases b <;> rfl
  have find_and_in_cone (D : Circuit) (hAO : IsAO2 26 D) :
      ∀ w : ℕ, w < 26 + D.gates.length →
        wireVal 26 D w e013 = true →
        wireVal 26 D w e0 = false →
        wireVal 26 D w e13 = false →
        ∃ a < D.gates.length,
          (26 + a = w ∨ (26 ≤ w ∧ InCone 26 D a (w - 26))) ∧
          (gateAt D a).op = GateOp.and ∧
          gateVal 26 D a e013 = true ∧
          gateVal 26 D a e0 = false ∧
          gateVal 26 D a e13 = false := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw_lt hw013 hw0 hw13
      by_cases hw26 : w < 26
      · exfalso
        have hr : wireVal 26 D w e013 = e013 ⟨w, hw26⟩ := wireVal_input D ⟨w, hw26⟩ e013
        rw [hr] at hw013
        rcases he013_true ⟨w, hw26⟩ hw013 with h0 | h13
        · change w = 0 at h0
          subst h0
          have h := wireVal_input D 0 e0
          change wireVal 26 D 0 e0 = e0 0 at h
          rw [he0_0] at h
          rw [h] at hw0
          cases hw0
        · change w = 13 at h13
          subst h13
          have h := wireVal_input D 13 e13
          change wireVal 26 D 13 e13 = e13 13 at h
          rw [he13_13] at h
          rw [h] at hw13
          cases hw13
      · let k : ℕ := w - 26
        have hwk : 26 + k = w := by omega
        have hk : k < D.gates.length := by omega
        have hmem : gateAt D k ∈ D.gates := by
          change D.gates.getD k ⟨GateOp.or, []⟩ ∈ D.gates
          rw [List.getD_eq_getElem _ _ hk]
          exact List.getElem_mem hk
        rcases hAO.1 (gateAt D k) hmem with hand | hor
        · refine ⟨k, hk, Or.inl hwk, hand, ?_, ?_, ?_⟩
          · change wireVal 26 D (26 + k) e013 = true; rwa [hwk]
          · change wireVal 26 D (26 + k) e0 = false; rwa [hwk]
          · change wireVal 26 D (26 + k) e13 = false; rwa [hwk]
        · obtain ⟨u, v, huv, hu_lt, hv_lt⟩ := isAO2_gate_inputs D hAO hk
          rw [← hwk] at hw013 hw0 hw13
          rw [wireVal_or_pair D hAO.2.1 hk hor huv e013, Bool.or_eq_true] at hw013
          rw [wireVal_or_pair D hAO.2.1 hk hor huv e0, Bool.or_eq_false_iff] at hw0
          rw [wireVal_or_pair D hAO.2.1 hk hor huv e13, Bool.or_eq_false_iff] at hw13
          rcases hw013 with huT | hvT
          · obtain ⟨a, ha_lt, ha_pos, ha_and, ha013, ha0, ha13⟩ :=
              ih u (by omega) (by omega) huT hw0.1 hw13.1
            have hu_mem : u ∈ (gateAt D k).inputs := by rw [huv]; exact List.mem_cons_self
            have hIn : InCone 26 D a k := by
              rw [inCone_iff D a k hk]
              rcases ha_pos with hEq | ⟨hu26, hInu⟩
              · exact ⟨u, hu_mem, by omega, hu_lt, Or.inl (by omega)⟩
              · exact ⟨u, hu_mem, hu26, hu_lt, Or.inr hInu⟩
            exact ⟨a, ha_lt, Or.inr ⟨by omega, hIn⟩, ha_and, ha013, ha0, ha13⟩
          · obtain ⟨a, ha_lt, ha_pos, ha_and, ha013, ha0, ha13⟩ :=
              ih v (by omega) (by omega) hvT hw0.2 hw13.2
            have hv_mem : v ∈ (gateAt D k).inputs := by
              rw [huv]; exact List.mem_cons_of_mem _ List.mem_cons_self
            have hIn : InCone 26 D a k := by
              rw [inCone_iff D a k hk]
              rcases ha_pos with hEq | ⟨hv26, hInv⟩
              · exact ⟨v, hv_mem, by omega, hv_lt, Or.inl (by omega)⟩
              · exact ⟨v, hv_mem, hv26, hv_lt, Or.inr hInv⟩
            exact ⟨a, ha_lt, Or.inr ⟨by omega, hIn⟩, ha_and, ha013, ha0, ha13⟩
  have hUncovOfDirty : ∀ (D : Circuit),
      D.size ≤ 64 →
      IsAO2 26 D →
      (∀ x : Fin 26 → Bool, D.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 13, I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
      (∃ d < D.gates.length, (gateAt D d).op = GateOp.and ∧
        ∃ y : Fin 26 → Bool, gateVal 26 D d y = true ∧ D.eval (List.ofFn y) = false) →
      ∃ p l : Fin 13, I p l ∧ ¬ ∃ k u v : ℕ,
        andOn D k u v ∧ orp D 26 (26 + k) D.output ∧
        orp D 26 p.val u ∧ orp D 26 (13 + l.val) v := by
    intro D hDsz hDAO2 hDpg hDdirty
    obtain ⟨d, hd_lt, hd_and, yd, hd_true, hD_yd_false⟩ := hDdirty
    by_contra hno
    have hall : ∀ p l : Fin 13, I p l →
        ∃ k u v : ℕ, andOn D k u v ∧ orp D 26 (26 + k) D.output ∧
          orp D 26 p.val u ∧ orp D 26 (13 + l.val) v := by
      intro p l hpl
      by_contra hnot
      exact hno ⟨p, l, hpl, hnot⟩
    have hNoC4 : ∀ (p1 p2 l1 l2 : Fin 13), p1 ≠ p2 → l1 ≠ l2 → ¬(I p1 l1 ∧ I p1 l2 ∧ I p2 l1 ∧ I p2 l2) := by
      have hI_mem (p l : Fin 13) (h : I p l) : p - l ∈ ([0, 1, 3, 9] : List (Fin 13)) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rcases h with rfl | rfl | rfl | rfl
        · exact Or.inl (sub_self _)
        · exact Or.inr (Or.inl (add_sub_cancel_left _ _))
        · exact Or.inr (Or.inr (Or.inl (add_sub_cancel_left _ _)))
        · exact Or.inr (Or.inr (Or.inr (add_sub_cancel_left _ _)))
      intro p1 p2 l1 l2 hp hl h
      obtain ⟨h11, h12, h21, h22⟩ := h
      apply hdiff_c4 (p1 - l1) (hI_mem p1 l1 h11) (p1 - l2) (hI_mem p1 l2 h12)
        (p2 - l1) (hI_mem p2 l1 h21) (p2 - l2) (hI_mem p2 l2 h22)
      · intro heq
        have h := congrArg (fun z => p1 - z) heq
        simp only [sub_sub_cancel] at h
        exact hl h
      · intro heq; exact hp (by simpa only [sub_add_cancel] using congrArg (· + l1) heq)
      · abel
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
        exact Prod.ext h2 (hidx4 a.2 b.2 hd)
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
        (∀ k < D.gates.length, (gateAt D k).op = GateOp.or →
          ∀ a ∈ (gateAt D k).inputs, Q a → Q (26 + k)) →
        Q w
    have orPath_refl (t : ℕ) : OrPath t t := fun _ h _ => h
    have orPath_step {k a t : ℕ} (hk : k < D.gates.length) (hor : (gateAt D k).op = GateOp.or)
        (ha : a ∈ (gateAt D k).inputs) (hp : OrPath a t) : OrPath (26 + k) t :=
      fun Q ht hs => hs k hk hor a ha (hp Q ht hs)
    have orPath_trans {u v w : ℕ} (huv : OrPath u v) (hvw : OrPath v w) : OrPath u w :=
      fun Q hw hs => huv Q (hvw Q hw hs) hs
    have orPath_cases {w t : ℕ} (h : OrPath w t) :
        w = t ∨ ∃ k < D.gates.length, w = 26 + k ∧ (gateAt D k).op = GateOp.or ∧
          ∃ a ∈ (gateAt D k).inputs, OrPath a t := by
      apply h (fun x => x = t ∨ ∃ k < D.gates.length, x = 26 + k ∧ (gateAt D k).op = GateOp.or ∧
          ∃ a ∈ (gateAt D k).inputs, OrPath a t)
      · exact Or.inl rfl
      · intro k hk hor a ha hPa
        refine Or.inr ⟨k, hk, rfl, hor, a, ha, ?_⟩
        rcases hPa with rfl | ⟨k', hk', rfl, hor', a', ha', hp'⟩
        · exact orPath_refl _
        · exact orPath_step hk' hor' ha' hp'
    have orPath_parent {w t : ℕ} (h : OrPath w t) (hne : w ≠ t) :
        ∃ y < D.gates.length, (gateAt D y).op = GateOp.or ∧
          OrPath w (26 + y) ∧ t ∈ (gateAt D y).inputs := by
      have hdisj : w = t ∨ ∃ y < D.gates.length, (gateAt D y).op = GateOp.or ∧
          OrPath w (26 + y) ∧ t ∈ (gateAt D y).inputs := by
        apply h (fun x => x = t ∨ ∃ y < D.gates.length, (gateAt D y).op = GateOp.or ∧
            OrPath x (26 + y) ∧ t ∈ (gateAt D y).inputs)
        · exact Or.inl rfl
        · intro k hk hor a ha hPa
          rcases hPa with rfl | ⟨y, hy, hory, hpy, hty⟩
          · exact Or.inr ⟨k, hk, hor, orPath_refl (26 + k), ha⟩
          · exact Or.inr ⟨y, hy, hory, orPath_step hk hor ha hpy, hty⟩
      rcases hdisj with heq | hex
      · exact (hne heq).elim
      · exact hex
    have orp_to_orPath {t w : ℕ} (h : PEqualNP.ReadTwo.orp D 26 t w) : OrPath w t := by
      change Relation.ReflTransGen (fun a b => a < b ∧ ∃ j, b = 26 + j ∧ isOr D j ∧ a ∈ (gateAt D j).inputs) t w at h
      induction h with
      | refl => exact orPath_refl t
      | tail _ hstep ih =>
        obtain ⟨_, j, rfl, ⟨hj, hor⟩, ha⟩ := hstep
        exact orPath_step hj hor ha ih
    have orPath_sound {w t : ℕ} (hp : OrPath w t) (x : Fin 26 → Bool)
        (ht : wireVal 26 D t x = true) : wireVal 26 D w x = true := by
      apply hp (fun u => wireVal 26 D u x = true) ht
      intro k hk hor a ha hva
      exact wireVal_or_mem D hDAO2.2.1 hk hor ha x hva
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
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        · intro h
          by_cases hcond : u ∈ B ∨ v ∈ B
          · exact Or.inl ⟨h, hcond⟩
          · exact Or.inr ⟨h, hcond⟩
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
        (S_gates : Finset (Fin D.gates.length))
        (opWire : Fin D.gates.length → ℕ)
        (hnonempty : ∀ j ∈ S_gates, ∃ x : X, OrPath (opWire j) (wireOf x)) :
        let reach (w : ℕ) : Finset X := Finset.univ.filter (fun x => OrPath w (wireOf x))
        let E_S : Finset X := S_gates.biUnion (fun j => reach (opWire j))
        let O_S : Finset (Fin D.gates.length) :=
          Finset.univ.filter (fun o =>
            (gateAt D o.val).op = GateOp.or ∧
            2 ≤ (reach (26 + o.val)).card ∧
            ∃ j ∈ S_gates, OrPath (opWire j) (26 + o.val))
        E_S.card ≤ O_S.card + S_gates.card := by
      let reach (w : ℕ) : Finset X := Finset.univ.filter (fun x => OrPath w (wireOf x))
      let E_S : Finset X := S_gates.biUnion (fun j => reach (opWire j))
      let O_S : Finset (Fin D.gates.length) :=
        Finset.univ.filter (fun o =>
          (gateAt D o.val).op = GateOp.or ∧
          2 ≤ (reach (26 + o.val)).card ∧
          ∃ j ∈ S_gates, OrPath (opWire j) (26 + o.val))
      let pairOf (o : Fin D.gates.length) : Option (X × X) :=
        let a := (gateAt D o.val).inputs.getD 0 0
        let b := (gateAt D o.val).inputs.getD 1 0
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
        obtain ⟨a, b, hab, _, _⟩ := isAO2_gate_inputs D hDAO2 o.isLt
        have ha_get : (gateAt D o.val).inputs.getD 0 0 = a := by rw [hab]; rfl
        have hb_get : (gateAt D o.val).inputs.getD 1 0 = b := by rw [hab]; rfl
        dsimp only [pairOf] at hpair_eq
        rw [ha_get, hb_get] at hpair_eq
        split_ifs at hpair_eq with hne
        injection hpair_eq with hpr_eq
        rw [← hpr_eq]
        have hu : hne.1.choose ∈ reach a := hne.1.choose_spec
        have hv : hne.2.choose ∈ reach b := hne.2.choose_spec
        have hua : OrPath a (wireOf hne.1.choose) := (Finset.mem_filter.mp hu).2
        have hvb : OrPath b (wireOf hne.2.choose) := (Finset.mem_filter.mp hv).2
        have ha_mem : a ∈ (gateAt D o.val).inputs := by rw [hab]; exact List.mem_cons_self
        have hb_mem : b ∈ (gateAt D o.val).inputs := by rw [hab]; exact List.mem_cons_of_mem _ List.mem_cons_self
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
            have hstep_ex : ∃ k < D.gates.length, w = 26 + k ∧ (gateAt D k).op = GateOp.or := by
              rcases orPath_cases hp1 with rfl | ⟨k, hk, hwk, hor, _⟩
              · rcases orPath_cases hp2 with h2 | ⟨k, hk, hwk, hor, _⟩
                · exact (hne_w h2).elim
                · exact ⟨k, hk, hwk, hor⟩
              · exact ⟨k, hk, hwk, hor⟩
            obtain ⟨k, hk, hwk, hor⟩ := hstep_ex
            let o : Fin D.gates.length := ⟨k, hk⟩
            have h2card : 2 ≤ (reach (26 + o.val)).card := by
              rw [← hwk]
              exact Finset.one_lt_card.mpr ⟨x1, hx1, x2, hx2, h12⟩
            have ho_mem : o ∈ O_S :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hor, h2card, j, hjS, hwk ▸ hjw⟩
            obtain ⟨a, b, hab, ha_lt, hb_lt⟩ := isAO2_gate_inputs D hDAO2 hk
            have ha_mem : a ∈ (gateAt D k).inputs := by rw [hab]; exact List.mem_cons_self
            have hb_mem : b ∈ (gateAt D k).inputs := by rw [hab]; exact List.mem_cons_of_mem _ List.mem_cons_self
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
                have ha_get : (gateAt D o.val).inputs.getD 0 0 = a := by rw [hab]; rfl
                have hb_get : (gateAt D o.val).inputs.getD 1 0 = b := by rw [hab]; rfl
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
                have ha_get : (gateAt D o.val).inputs.getD 0 0 = a := by rw [hab]; rfl
                have hb_get : (gateAt D o.val).inputs.getD 1 0 = b := by rw [hab]; rfl
                rw [ha_get, hb_get]; split_ifs; rfl
              obtain ⟨B1, hB1Q, hx2B1, huB1⟩ := ih a (by omega) ⟨j, hjS, hja⟩ x2 h2a hne_ab.1.choose hne_ab.1.choose_spec
              obtain ⟨B2, hB2Q, huB2, hvB2⟩ := hQ_pairs _ hpair_in
              obtain ⟨B3, hB3Q, hvB3, hx1B3⟩ := ih b (by omega) ⟨j, hjS, hjb⟩ hne_ab.2.choose hne_ab.2.choose_spec x1 h1b
              have h12B := partition_unique_block hQ_part hB1Q hB2Q huB1 huB2
              have h23B := partition_unique_block hQ_part hB2Q hB3Q hvB2 hvB3
              subst h12B; subst h23B
              exact ⟨B1, hB1Q, hx1B3, hx2B1⟩
            · exact ih b (by omega) ⟨j, hjS, hjb⟩ x1 h1b x2 h2b
      let blk (j : Fin D.gates.length) : Finset X :=
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
        wireVal 26 D D.output x = true ↔
          ∃ (p l : Fin 13), (p, l) ∈ E ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
      have h := hDpg x
      change wireVal 26 D D.output x = true ↔ _ at h
      rw [h]
      simp only [hmem_E]
    have hno_pts_only (x : Fin 26 → Bool) (h0 : ∀ l : Fin 13, x (Fin.natAdd 13 l) = false) :
        wireVal 26 D D.output x = false := by
      cases hv : wireVal 26 D D.output x
      · rfl
      · obtain ⟨_, l, _, _, hl⟩ := (hComp_wire x).mp hv
        rw [h0 l] at hl; cases hl
    have hno_lns_only (x : Fin 26 → Bool) (h0 : ∀ p : Fin 13, x (Fin.castAdd 13 p) = false) :
        wireVal 26 D D.output x = false := by
      cases hv : wireVal 26 D D.output x
      · rfl
      · obtain ⟨p, _, _, hp, _⟩ := (hComp_wire x).mp hv
        rw [h0 p] at hp; cases hp
    have hedge_covered : ∀ p l : Fin 13, (p, l) ∈ E →
        ∃ j : Fin D.gates.length, (gateAt D j.val).op = GateOp.and ∧
          OrPath D.output (26 + j.val) ∧
          ∃ a b : ℕ, (gateAt D j.val).inputs = [a, b] ∧
            ((OrPath a p.val ∧ OrPath b (13 + l.val)) ∨
             (OrPath a (13 + l.val) ∧ OrPath b p.val)) := by
      intro p l hpl
      obtain ⟨j, a, b, handOn, htop, hpa, hlb⟩ := hall p l ((hmem_E p l).mp hpl)
      obtain ⟨⟨hjlt, hjand⟩, hor_ab⟩ := handOn
      obtain ⟨a0, b0, hab0, _, _⟩ := isAO2_gate_inputs D hDAO2 hjlt
      have hin0 : in0 D j = a0 := by change (gateAt D j).inputs.getD 0 0 = a0; rw [hab0]; rfl
      have hin1 : in1 D j = b0 := by change (gateAt D j).inputs.getD 1 0 = b0; rw [hab0]; rfl
      refine ⟨⟨j, hjlt⟩, hjand, orp_to_orPath htop, a0, b0, hab0, ?_⟩
      rcases hor_ab with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · rw [hin0] at h0; rw [hin1] at h1; subst h0; subst h1
        exact Or.inl ⟨orp_to_orPath hpa, orp_to_orPath hlb⟩
      · rw [hin0] at h0; rw [hin1] at h1; subst h0; subst h1
        exact Or.inr ⟨orp_to_orPath hlb, orp_to_orPath hpa⟩
    let Tstar : Finset (Fin D.gates.length) :=
      Finset.univ.filter (fun j =>
        (gateAt D j.val).op = GateOp.and ∧
        OrPath D.output (26 + j.val) ∧
        ∃ p l : Fin 13, ∃ a b : ℕ, (gateAt D j.val).inputs = [a, b] ∧
          ((OrPath a p.val ∧ OrPath b (13 + l.val)) ∨
           (OrPath a (13 + l.val) ∧ OrPath b p.val)))
    let pWire (j : Fin D.gates.length) : ℕ :=
      let a := (gateAt D j.val).inputs.getD 0 0
      let b := (gateAt D j.val).inputs.getD 1 0
      if (pts a).Nonempty then a else b
    let lWire (j : Fin D.gates.length) : ℕ :=
      let a := (gateAt D j.val).inputs.getD 0 0
      let b := (gateAt D j.val).inputs.getD 1 0
      if (pts a).Nonempty then b else a
    let pSide (j : Fin D.gates.length) : Finset (Fin 13) := pts (pWire j)
    let lSide (j : Fin D.gates.length) : Finset (Fin 13) := lns (lWire j)
    have hTstar_props : ∀ j ∈ Tstar,
        (gateAt D j.val).op = GateOp.and ∧
        OrPath D.output (26 + j.val) ∧
        (pSide j).Nonempty ∧ (lSide j).Nonempty ∧
        lns (pWire j) = ∅ ∧ pts (lWire j) = ∅ ∧
        (∀ p ∈ pSide j, ∀ l ∈ lSide j, (p, l) ∈ E) ∧
        ((pSide j).card = 1 ∨ (lSide j).card = 1) := by
      intro j hj
      obtain ⟨hand, htop, p0, l0, a, b, hab, hlr0⟩ := (Finset.mem_filter.mp hj).2
      have ha_get : (gateAt D j.val).inputs.getD 0 0 = a := by rw [hab]; rfl
      have hb_get : (gateAt D j.val).inputs.getD 1 0 = b := by rw [hab]; rfl
      have hand_sound : ∀ x : Fin 26 → Bool,
          wireVal 26 D a x = true → wireVal 26 D b x = true → wireVal 26 D D.output x = true := by
        intro x hxa hxb
        apply orPath_sound htop x
        rw [wireVal_and_pair D hDAO2.2.1 j.isLt hand hab x, hxa, hxb]
        rfl
      have hno_both_pts : ¬ ((pts a).Nonempty ∧ (pts b).Nonempty) := by
        rintro ⟨⟨p1, hp1⟩, ⟨p2, hp2⟩⟩
        let x : Fin 26 → Bool := fun i => decide (i = Fin.castAdd 13 p1 ∨ i = Fin.castAdd 13 p2)
        have h1 : wireVal 26 D p1.val x = true := by
          have := wireVal_input D (Fin.castAdd 13 p1) x
          simpa [x] using this
        have h2 : wireVal 26 D p2.val x = true := by
          have := wireVal_input D (Fin.castAdd 13 p2) x
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
        have h1 : wireVal 26 D (13 + l1.val) x = true := by
          have := wireVal_input D (Fin.natAdd 13 l1) x
          simpa [x, Nat.add_comm] using this
        have h2 : wireVal 26 D (13 + l2.val) x = true := by
          have := wireVal_input D (Fin.natAdd 13 l2) x
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
        have hxp : wireVal 26 D p.val x = true := by
          have := wireVal_input D (Fin.castAdd 13 p) x
          simpa [x] using this
        have hxl : wireVal 26 D (13 + l.val) x = true := by
          have := wireVal_input D (Fin.natAdd 13 l) x
          simpa [x, Nat.add_comm] using this
        have hout_t : wireVal 26 D D.output x = true := by
          rcases hpl with ⟨hpa, hlb⟩ | ⟨hpb, hla⟩
          · exact hand_sound x
              (orPath_sound (Finset.mem_filter.mp hpa).2 x hxp)
              (orPath_sound (Finset.mem_filter.mp hlb).2 x hxl)
          · exact hand_sound x
              (orPath_sound (Finset.mem_filter.mp hla).2 x hxl)
              (orPath_sound (Finset.mem_filter.mp hpb).2 x hxp)
        obtain ⟨p', l', hp'l', hxp', hxl'⟩ := (hComp_wire x).mp hout_t
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
      have ha_get : (gateAt D j.val).inputs.getD 0 0 = a := by rw [hab]; rfl
      have hb_get : (gateAt D j.val).inputs.getD 1 0 = b := by rw [hab]; rfl
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
    let Tpt : Finset (Fin D.gates.length) := Tstar.filter (fun j => (pSide j).card = 1)
    let Tln : Finset (Fin D.gates.length) := Tstar.filter (fun j => (pSide j).card ≠ 1)
    have hTpt_Tln_disj : Disjoint Tpt Tln := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    have hTpt_Tln_union : Tpt ∪ Tln = Tstar := by
      ext j
      simp only [Tpt, Tln, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        by_cases hc : (pSide j).card = 1
        · exact Or.inl ⟨h, hc⟩
        · exact Or.inr ⟨h, hc⟩
    have hTstar_split : Tpt.card + Tln.card = Tstar.card := by
      rw [← Finset.card_union_of_disjoint hTpt_Tln_disj, hTpt_Tln_union]
    let centerP (j : Fin D.gates.length) : Fin 13 :=
      if h : (pSide j).Nonempty then h.choose else 0
    let centerL (j : Fin D.gates.length) : Fin 13 :=
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
    let Otop : Finset (Fin D.gates.length) :=
      Finset.univ.filter (fun o =>
        (gateAt D o.val).op = GateOp.or ∧
        OrPath D.output (26 + o.val) ∧
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
        have hroot_ex : ∃ root ∈ Otop, D.output = 26 + root.val := by
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
            ∃ y ∈ Otop, 26 + x.val ∈ (gateAt D y.val).inputs := by
          intro x hx
          have hxne : x ≠ root := (Finset.mem_erase.mp hx).1
          have hxH : x ∈ H := (Finset.mem_erase.mp hx).2
          have hx_out : OrPath D.output (26 + x.val) := by
            rcases Finset.mem_union.mp hxH with hO | hT
            · exact (Finset.mem_filter.mp hO).2.2.1
            · exact (hTstar_props x hT).2.1
          have hx_a : ∃ a ∈ Tstar, OrPath (26 + x.val) (26 + a.val) := by
            rcases Finset.mem_union.mp hxH with hO | hT
            · exact (Finset.mem_filter.mp hO).2.2.2
            · exact ⟨x, hT, orPath_refl _⟩
          have hne_out : D.output ≠ 26 + x.val := by
            rw [hroot_eq]; intro h; exact hxne (Fin.ext (by omega))
          obtain ⟨y, hy, hory, hpy, hxin⟩ := orPath_parent hx_out hne_out
          obtain ⟨a, haT, hxa⟩ := hx_a
          refine ⟨⟨y, hy⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hory, hpy,
            a, haT, orPath_step hy hory hxin hxa⟩, hxin⟩
        let par (x : Fin D.gates.length) : Fin D.gates.length :=
          if hx : x ∈ H.erase root then (hpar_ex x hx).choose else root
        have hpar_mem : ∀ x ∈ H.erase root, par x ∈ Otop := by
          intro x hx; dsimp only [par]; simp only [hx, ↓reduceDIte]; exact (hpar_ex x hx).choose_spec.1
        have hpar_in : ∀ x ∈ H.erase root, 26 + x.val ∈ (gateAt D (par x).val).inputs := by
          intro x hx; dsimp only [par]; simp only [hx, ↓reduceDIte]; exact (hpar_ex x hx).choose_spec.2
        have hfiber_le2 : ∀ y ∈ Otop, ((H.erase root).filter (fun x => par x = y)).card ≤ 2 := by
          intro y _
          let F := (H.erase root).filter (fun x => par x = y)
          have hsub : F.image (fun x : Fin D.gates.length => 26 + x.val) ⊆ (gateAt D y.val).inputs.toFinset := by
            intro w hw
            obtain ⟨x, hxF, rfl⟩ := Finset.mem_image.mp hw
            obtain ⟨hxH, hxy⟩ := Finset.mem_filter.mp hxF
            rw [List.mem_toFinset, ← hxy]
            exact hpar_in x hxH
          have hinj : Function.Injective (fun x : Fin D.gates.length => 26 + x.val) := by
            intro a b h; dsimp only at h; exact Fin.ext (by omega)
          have h1 : F.card = (F.image (fun x : Fin D.gates.length => 26 + x.val)).card :=
            (Finset.card_image_of_injective F hinj).symm
          have h2 : (F.image (fun x : Fin D.gates.length => 26 + x.val)).card ≤ ((gateAt D y.val).inputs.toFinset).card :=
            Finset.card_le_card hsub
          have h3 : ((gateAt D y.val).inputs.toFinset).card ≤ (gateAt D y.val).inputs.length :=
            List.toFinset_card_le _
          have h4 : (gateAt D y.val).inputs.length = 2 := by
            obtain ⟨a, b, hab, _, _⟩ := isAO2_gate_inputs D hDAO2 y.isLt
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
    let Tpt_p (p : Fin 13) : Finset (Fin D.gates.length) := Tpt.filter (fun j => centerP j = p)
    let E_p (p : Fin 13) : Finset (Fin 13) := (Tpt_p p).biUnion lSide
    let Obot_p (p : Fin 13) : Finset (Fin D.gates.length) :=
      Finset.univ.filter (fun o =>
        (gateAt D o.val).op = GateOp.or ∧
        2 ≤ (lns (26 + o.val)).card ∧
        ∃ j ∈ Tpt_p p, OrPath (lWire j) (26 + o.val))
    let Tln_l (l : Fin 13) : Finset (Fin D.gates.length) := Tln.filter (fun j => centerL j = l)
    let E_l (l : Fin 13) : Finset (Fin 13) := (Tln_l l).biUnion pSide
    let Obot_l (l : Fin 13) : Finset (Fin D.gates.length) :=
      Finset.univ.filter (fun o =>
        (gateAt D o.val).op = GateOp.or ∧
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
        have hx_l : wireVal 26 D (13 + l0.val) x = true := by
          have := wireVal_input D (Fin.natAdd 13 l0) x
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
        have hx_p : wireVal 26 D p0.val x = true := by
          have := wireVal_input D (Fin.castAdd 13 p0) x
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
    let dFin : Fin D.gates.length := ⟨d, hd_lt⟩
    have hdNotIn : dFin ∉ (Tstar ∪ Obot) ∪ Otop := by
      intro hmem
      rcases Finset.mem_union.mp hmem with h1 | hO
      · rcases Finset.mem_union.mp h1 with hT | hB
        · have hop := (hTstar_props dFin hT).2.1
          have hwt : wireVal 26 D D.output yd = true := orPath_sound hop yd hd_true
          change wireVal 26 D D.output yd = false at hD_yd_false
          rw [hwt] at hD_yd_false
          cases hD_yd_false
        · rcases Finset.mem_union.mp hB with hBA | hBB
          · obtain ⟨_, _, ho⟩ := Finset.mem_biUnion.mp hBA
            have hor := (Finset.mem_filter.mp ho).2.1
            change (gateAt D d).op = GateOp.or at hor
            rw [hd_and] at hor; cases hor
          · obtain ⟨_, _, ho⟩ := Finset.mem_biUnion.mp hBB
            have hor := (Finset.mem_filter.mp ho).2.1
            change (gateAt D d).op = GateOp.or at hor
            rw [hd_and] at hor; cases hor
      · have hor := (Finset.mem_filter.mp hO).2.1
        change (gateAt D d).op = GateOp.or at hor
        rw [hd_and] at hor; cases hor
    have h4disj : Tstar.card + Obot.card + Otop.card + 1 ≤ D.size := by
      have hdisj1 : Disjoint (Tstar ∪ Obot) Otop := by
        rw [Finset.disjoint_union_left]
        exact ⟨hOtop_disj_Tstar.symm, hObot_disj_Otop⟩
      have hcard_u : ((Tstar ∪ Obot) ∪ Otop).card = Tstar.card + Obot.card + Otop.card := by
        rw [Finset.card_union_of_disjoint hdisj1, Finset.card_union_of_disjoint hObot_disj_Tstar.symm]
      have hcard_ins : (insert dFin ((Tstar ∪ Obot) ∪ Otop)).card = ((Tstar ∪ Obot) ∪ Otop).card + 1 :=
        Finset.card_insert_of_notMem hdNotIn
      have hle : (insert dFin ((Tstar ∪ Obot) ∪ Otop)).card ≤ (Finset.univ : Finset (Fin D.gates.length)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      simp only [Finset.card_univ, Fintype.card_fin] at hle
      change Tstar.card + Obot.card + Otop.card + 1 ≤ D.gates.length
      omega
    omega
  rintro ⟨C, hsz64, hGates, hPG_sub, hDirty, i, j, hij_ne, hnij, hnji, hi_spec, hj_spec⟩
  have hAO : IsAO2 26 C := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
      exact (hGates k C.gates[k] (List.getElem?_eq_getElem hk)).1
    · intro k hk u hu
      have h := (hGates k C.gates[k] (List.getElem?_eq_getElem hk)).2
      obtain ⟨a, b, hab, _, ha, hb⟩ := h
      have hgat : gateAt C k = C.gates[k] := by
        change C.gates.getD k ⟨GateOp.or, []⟩ = C.gates[k]
        exact List.getD_eq_getElem _ _ hk
      rw [hgat, hab] at hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact ha
      · exact hb
    · intro g hg
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
      obtain ⟨a, b, hab, _, _, _⟩ := (hGates k C.gates[k] (List.getElem?_eq_getElem hk)).2
      rw [hab]; rfl
  have hNodup : ∀ g ∈ C.gates, g.inputs.Nodup := by
    intro g hg
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨a, b, hab, hne, _, _⟩ := (hGates k C.gates[k] (List.getElem?_eq_getElem hk)).2
    rw [hab, List.nodup_cons, List.mem_singleton]
    exact ⟨hne, List.nodup_singleton b⟩
  have hPG : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 13, I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
    intro x
    rw [hPG_sub x]
    constructor
    · rintro ⟨p, l, hmem, hp, hl⟩
      exact ⟨p, l, (hpg_sub_iff p l).mp hmem, hp, hl⟩
    · rintro ⟨p, l, hpl, hp, hl⟩
      exact ⟨p, l, (hpg_sub_iff p l).mpr hpl, hp, hl⟩
  have hgate_lt_of_and : ∀ (D : Circuit) (k : ℕ), (gateAt D k).op = GateOp.and → k < D.gates.length := by
    intro D k hand
    by_contra hge
    have hdef : gateAt D k = ⟨GateOp.or, []⟩ := by
      change D.gates.getD k ⟨GateOp.or, []⟩ = ⟨GateOp.or, []⟩
      exact List.getD_eq_default _ _ (by omega)
    rw [hdef] at hand
    cases hand
  have hi_lt : i < C.gates.length := hgate_lt_of_and C i hi_spec.1
  have hj_lt : j < C.gates.length := hgate_lt_of_and C j hj_spec.1
  let Good : Circuit → ℕ → ℕ → Prop := fun D u v =>
    D.size ≤ 64 ∧ IsAO2 26 D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
    (∀ x : Fin 26 → Bool, D.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 13, I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) ∧
    (∃ d < D.gates.length, (gateAt D d).op = GateOp.and ∧
      ∃ y : Fin 26 → Bool, gateVal 26 D d y = true ∧ D.eval (List.ofFn y) = false) ∧
    u < D.gates.length ∧ v < D.gates.length ∧ u ≠ v ∧ ¬ InCone 26 D u v ∧ ¬ InCone 26 D v u ∧
    (gateAt D u).op = GateOp.and ∧ (26 + u = D.output ∨ InCone 26 D u (D.output - 26)) ∧
    gateVal 26 D u e013 = true ∧ (∀ b : Fin 2, wireVal 26 D (opnd D u b) e0 = false) ∧
    (gateAt D v).op = GateOp.and ∧ (26 + v = D.output ∨ InCone 26 D v (D.output - 26)) ∧
    gateVal 26 D v e013 = true ∧ (∀ b : Fin 2, wireVal 26 D (opnd D v b) e13 = false)
  have hGood0 : Good C i j :=
    ⟨hsz64, hAO, hNodup, hPG, hDirty, hi_lt, hj_lt, hij_ne, hnij, hnji,
     hi_spec.1, hi_spec.2.1, hi_spec.2.2.1, hi_spec.2.2.2,
     hj_spec.1, hj_spec.2.1, hj_spec.2.2.1, hj_spec.2.2.2⟩
  have hOut_bounds : ∀ (D : Circuit),
      (∀ x : Fin 26 → Bool, D.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 13, I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
      26 ≤ D.output ∧ D.output < 26 + D.gates.length ∧
        wireVal 26 D D.output e013 = true ∧
        wireVal 26 D D.output e0 = false ∧
        wireVal 26 D D.output e13 = false := by
    intro D hDpg
    have h013 : wireVal 26 D D.output e013 = true := by
      change D.eval (List.ofFn e013) = true
      exact (hDpg e013).mpr ⟨0, 0, Or.inl rfl, by decide, by decide⟩
    have h0 : wireVal 26 D D.output e0 = false := by
      cases hv : wireVal 26 D D.output e0
      · rfl
      · change D.eval (List.ofFn e0) = true at hv
        obtain ⟨p, l, _, _, hl⟩ := (hDpg e0).mp hv
        have hbad : ∀ l' : Fin 13, e0 (Fin.natAdd 13 l') = false := by decide
        rw [hbad l] at hl; cases hl
    have h13 : wireVal 26 D D.output e13 = false := by
      cases hv : wireVal 26 D D.output e13
      · rfl
      · change D.eval (List.ofFn e13) = true at hv
        obtain ⟨p, l, _, hp, _⟩ := (hDpg e13).mp hv
        have hbad : ∀ p' : Fin 13, e13 (Fin.castAdd 13 p') = false := by decide
        rw [hbad p] at hp; cases hp
    have hge26 : 26 ≤ D.output := by
      by_contra hlt26
      have hr : wireVal 26 D D.output e013 = e013 ⟨D.output, by omega⟩ :=
        wireVal_input D ⟨D.output, by omega⟩ e013
      rw [hr] at h013
      rcases he013_true ⟨D.output, by omega⟩ h013 with hz | h13'
      · change D.output = 0 at hz
        have h := wireVal_input D 0 e0
        change wireVal 26 D 0 e0 = e0 0 at h
        rw [he0_0] at h
        rw [hz, h] at h0; cases h0
      · change D.output = 13 at h13'
        have h := wireVal_input D 13 e13
        change wireVal 26 D 13 e13 = e13 13 at h
        rw [he13_13] at h
        rw [h13', h] at h13; cases h13
    have hlt_len : D.output < 26 + D.gates.length := by
      by_contra hge
      have hlen : (run D.gates (List.ofFn e013)).length = 26 + D.gates.length := by
        rw [run_len, List.length_ofFn]
      have hdef : wireVal 26 D D.output e013 = false := by
        change (run D.gates (List.ofFn e013)).getD D.output false = false
        exact List.getD_eq_default _ false (n := D.output) (by omega)
      rw [hdef] at h013; cases h013
    exact ⟨hge26, hlt_len, h013, h0, h13⟩
  have hGoodDual : ∀ (D : Circuit) (u v : ℕ), Good D u v →
      Good (dualCirc D) v u ∧
      gateVal 26 (dualCirc D) v e13 = gateVal 26 D v e0 ∧
      gateVal 26 (dualCirc D) u e0 = gateVal 26 D u e13 := by
    intro D u v hG
    obtain ⟨hsz, hDAO, hDnd, hDpg, ⟨d, hd_lt, hd_and, yd, hdy_t, hD_yd_f⟩,
      hu_lt, hv_lt, huv_ne, hnuv, hnvu,
      hu_and, hu_live, hu_013, hu_e0,
      hv_and, hv_live, hv_013, hv_e13⟩ := hG
    have hout_ge26 : 26 ≤ D.output := (hOut_bounds D hDpg).1
    have hout_eq : (dualCirc D).output = D.output := hdual_ge26 D.output hout_ge26
    have hDual_len : (dualCirc D).gates.length = D.gates.length := List.length_map _
    have hDual_AO : IsAO2 26 (dualCirc D) := by
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
        exact hDAO.1 g0 hg0
      · intro k hk w hw
        rw [hDual_len] at hk
        rw [gateAt_dual D k hk] at hw
        obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw
        exact hdual_lt_add k w0 (hDAO.2.1 k hk w0 hw0)
      · intro g hg
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
        dsimp only [dualGate]
        rw [List.length_map]
        exact hDAO.2.2 g0 hg0
    have hDual_nd : ∀ g ∈ (dualCirc D).gates, g.inputs.Nodup := by
      intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      exact (hDnd g0 hg0).map hdual_inj
    have hDual_pg : ∀ x : Fin 26 → Bool, (dualCirc D).eval (List.ofFn x) = true ↔
        ∃ p l : Fin 13, I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
      intro x
      change wireVal 26 (dualCirc D) (dualCirc D).output x = true ↔ _
      rw [wireVal_dual, hout_eq, hdual_ge26 D.output hout_ge26]
      change D.eval (List.ofFn fun i => x (dual13f i)) = true ↔ _
      rw [hDpg (fun i => x (dual13f i))]
      constructor
      · rintro ⟨p, l, hpl, hp, hl⟩
        rw [hdual_cast p] at hp
        rw [hdual_nat l] at hl
        exact ⟨-l, -p, (hpg_neg p l).mp hpl, hl, hp⟩
      · rintro ⟨p, l, hpl, hp, hl⟩
        refine ⟨-l, -p, (hpg_neg (-l) (-p)).mpr (by simpa only [neg_neg] using hpl), ?_, ?_⟩
        · rw [hdual_cast (-l), neg_neg]; exact hl
        · rw [hdual_nat (-p), neg_neg]; exact hp
    have hDual_gv : ∀ (k : ℕ) (x : Fin 26 → Bool),
        gateVal 26 (dualCirc D) k x = gateVal 26 D k (fun i => x (dual13f i)) := by
      intro k x
      change wireVal 26 (dualCirc D) (26 + k) x = wireVal 26 D (26 + k) (fun i => x (dual13f i))
      rw [wireVal_dual, hdual_ge26 (26 + k) (by omega)]
    have hDual_dirty : ∃ d' < (dualCirc D).gates.length, (gateAt (dualCirc D) d').op = GateOp.and ∧
        ∃ y : Fin 26 → Bool, gateVal 26 (dualCirc D) d' y = true ∧ (dualCirc D).eval (List.ofFn y) = false := by
      let yd' : Fin 26 → Bool := fun i => yd (dual13f i)
      have hyd_comp : (fun i : Fin 26 => yd' (dual13f i)) = yd := by
        funext i
        dsimp only [yd', dual13f]
        congr 1
        exact Fin.ext (hdual_inv_fin i)
      refine ⟨d, by omega, ?_, yd', ?_, ?_⟩
      · rw [gateAt_dual D d hd_lt]; exact hd_and
      · rw [hDual_gv d yd', hyd_comp]; exact hdy_t
      · change wireVal 26 (dualCirc D) (dualCirc D).output yd' = false
        rw [wireVal_dual, hout_eq, hdual_ge26 D.output hout_ge26, hyd_comp]
        exact hD_yd_f
    refine ⟨⟨?_, hDual_AO, hDual_nd, hDual_pg, hDual_dirty,
        by omega, by omega, huv_ne.symm, ?_, ?_,
        ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · change D.gates.length ≤ 64 at hsz
      change (dualCirc D).gates.length ≤ 64
      omega
    · rw [inCone_dual]; exact hnvu
    · rw [inCone_dual]; exact hnuv
    · rw [gateAt_dual D v hv_lt]; exact hv_and
    · rw [hout_eq, inCone_dual]; exact hv_live
    · rw [hDual_gv v e013, hdual_e013]; exact hv_013
    · intro b
      rw [opnd_dual D hDAO v hv_lt b, wireVal_dual, hdual_inv, hdual_e0]
      exact hv_e13 b
    · rw [gateAt_dual D u hu_lt]; exact hu_and
    · rw [hout_eq, inCone_dual]; exact hu_live
    · rw [hDual_gv u e013, hdual_e013]; exact hu_013
    · intro b
      rw [opnd_dual D hDAO u hu_lt b, wireVal_dual, hdual_inv, hdual_e13]
      exact hu_e0 b
    · rw [hDual_gv v e13, hdual_e13]
    · rw [hDual_gv u e0, hdual_e0]
  have hFinishUnit : ∀ (D : Circuit) (u v : ℕ), Good D u v → gateVal 26 D u e13 = true → False := by
    intro D u v hG hu13
    obtain ⟨hsz, hDAO, hDnd, hDpg, hDdirty,
      hu_lt, hv_lt, huv_ne, hnuv, hnvu,
      hu_and, hu_live, hu_013, hu_e0,
      hv_and, hv_live, hv_013, hv_e13⟩ := hG
    have huncov := hUncovOfDirty D hsz hDAO hDpg hDdirty
    have hThird : ∃ a < D.gates.length, a ≠ u ∧ a ≠ v ∧
        (gateAt D a).op = GateOp.and ∧
        (26 + a = D.output ∨ InCone 26 D a (D.output - 26)) ∧
        gateVal 26 D a e013 = true ∧ gateVal 26 D a e0 = false ∧ gateVal 26 D a e13 = false := by
      cases hv0 : gateVal 26 D v e0 with
      | true =>
        obtain ⟨hout_ge26, hout_lt, hout_013, hout_0, hout_13⟩ := hOut_bounds D hDpg
        obtain ⟨a, ha_lt, ha_pos, ha_and, ha013, ha0, ha13⟩ :=
          find_and_in_cone D hDAO D.output hout_lt hout_013 hout_0 hout_13
        have ha_live : 26 + a = D.output ∨ InCone 26 D a (D.output - 26) := by
          rcases ha_pos with hEq | ⟨_, hIn⟩
          · exact Or.inl hEq
          · exact Or.inr hIn
        have hau : a ≠ u := by
          intro h; subst h; rw [ha13] at hu13; cases hu13
        have hav : a ≠ v := by
          intro h; subst h; rw [ha0] at hv0; cases hv0
        exact ⟨a, ha_lt, hau, hav, ha_and, ha_live, ha013, ha0, ha13⟩
      | false =>
        obtain ⟨w0, w1, hwv, hw0_lt, hw1_lt⟩ := isAO2_gate_inputs D hDAO hv_lt
        have hop0 : opnd D v 0 = w0 := by change (gateAt D v).inputs.getD 0 0 = w0; rw [hwv]; rfl
        have hop1 : opnd D v 1 = w1 := by change (gateAt D v).inputs.getD 1 0 = w1; rw [hwv]; rfl
        have hw0_13 : wireVal 26 D w0 e13 = false := by rw [← hop0]; exact hv_e13 0
        have hw1_13 : wireVal 26 D w1 e13 = false := by rw [← hop1]; exact hv_e13 1
        have hw_013 : wireVal 26 D w0 e013 = true ∧ wireVal 26 D w1 e013 = true := by
          have h := hv_013
          change wireVal 26 D (26 + v) e013 = true at h
          rw [wireVal_and_pair D hDAO.2.1 hv_lt hv_and hwv e013, Bool.and_eq_true] at h
          exact h
        have hw_0 : wireVal 26 D w0 e0 = false ∨ wireVal 26 D w1 e0 = false := by
          have h := hv0
          change wireVal 26 D (26 + v) e0 = false at h
          rw [wireVal_and_pair D hDAO.2.1 hv_lt hv_and hwv e0, Bool.and_eq_false_iff] at h
          exact h
        have hFromOp : ∀ (w : ℕ), w ∈ (gateAt D v).inputs → w < 26 + v →
            wireVal 26 D w e013 = true → wireVal 26 D w e0 = false → wireVal 26 D w e13 = false →
            ∃ a < D.gates.length, InCone 26 D a v ∧ (gateAt D a).op = GateOp.and ∧
              gateVal 26 D a e013 = true ∧ gateVal 26 D a e0 = false ∧ gateVal 26 D a e13 = false := by
          intro w hw_mem hw_lt hw013 hw0_f hw13_f
          obtain ⟨a, ha_lt, ha_pos, ha_and, ha013, ha0, ha13⟩ :=
            find_and_in_cone D hDAO w (by omega) hw013 hw0_f hw13_f
          have hIn : InCone 26 D a v := by
            rw [inCone_iff D a v hv_lt]
            rcases ha_pos with hEq | ⟨hw26, hInw⟩
            · exact ⟨w, hw_mem, by omega, hw_lt, Or.inl (by omega)⟩
            · exact ⟨w, hw_mem, hw26, hw_lt, Or.inr hInw⟩
          exact ⟨a, ha_lt, hIn, ha_and, ha013, ha0, ha13⟩
        have hex : ∃ a < D.gates.length, InCone 26 D a v ∧ (gateAt D a).op = GateOp.and ∧
            gateVal 26 D a e013 = true ∧ gateVal 26 D a e0 = false ∧ gateVal 26 D a e13 = false := by
          rcases hw_0 with h0f | h1f
          · exact hFromOp w0 (by rw [hwv]; exact List.mem_cons_self) hw0_lt hw_013.1 h0f hw0_13
          · exact hFromOp w1 (by rw [hwv]; exact List.mem_cons_of_mem _ List.mem_cons_self) hw1_lt hw_013.2 h1f hw1_13
        obtain ⟨a, ha_lt, hInv, ha_and, ha013, ha0, ha13⟩ := hex
        have hav : a ≠ v := by
          have hlt := (inCone_lt D v a hInv).1
          omega
        have hau : a ≠ u := by
          intro h; subst h; exact hnuv hInv
        have ha_live : 26 + a = D.output ∨ InCone 26 D a (D.output - 26) := by
          rcases hv_live with hEq | hOutv
          · exact Or.inr (by rw [← hEq, Nat.add_sub_cancel_left]; exact hInv)
          · exact Or.inr (inCone_trans D (D.output - 26) a v hInv hOutv)
        exact ⟨a, ha_lt, hau, hav, ha_and, ha_live, ha013, ha0, ha13⟩
    obtain ⟨a, ha_lt, hau, hav, ha_and, ha_live, ha013, ha0, ha13⟩ := hThird
    have hDpgS : ∀ x : Fin 26 → Bool, D.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 13, p - l ∈ ({(0 : Fin 13), 1, 3, 9} : Finset (Fin 13)) ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
      intro x; rw [hDpg x]
      constructor
      · rintro ⟨p, l, h, hp, hl⟩; exact ⟨p, l, (hpg_sub_iff p l).mpr h, hp, hl⟩
      · rintro ⟨p, l, h, hp, hl⟩; exact ⟨p, l, (hpg_sub_iff p l).mp h, hp, hl⟩
    obtain ⟨pu, lu, hpulu, huncov_body⟩ := huncov
    have huncovS : ∃ p l : Fin 13, p - l ∈ ({(0 : Fin 13), 1, 3, 9} : Finset (Fin 13)) ∧
        ¬ ∃ k u v : ℕ, andOn D k u v ∧ orp D 26 (26 + k) D.output ∧
          orp D 26 p.val u ∧ orp D 26 (13 + l.val) v :=
      ⟨pu, lu, (hpg_sub_iff pu lu).mpr hpulu, huncov_body⟩
    by_cases h63 : D.size ≤ 63
    · exact hLe63Unit D h63 hDAO hDnd hDpgS huncovS a u v hau hav huv_ne hnuv hnvu
        ⟨⟨ha_lt, ha_and⟩, ha_live, ha013⟩ ⟨⟨hu_lt, hu_and⟩, hu_live, hu_013⟩ ⟨⟨hv_lt, hv_and⟩, hv_live, hv_013⟩
        ha0 ha13 hu13 hu_e0 hv_e13
    · have h64 : D.size = 64 := by omega
      exact hEq64Unit D h64 hDAO hDnd hDpgS huncovS a u v hau hav huv_ne hnuv hnvu
        ⟨⟨ha_lt, ha_and⟩, ha_live, ha013⟩ ⟨⟨hu_lt, hu_and⟩, hu_live, hu_013⟩ ⟨⟨hv_lt, hv_and⟩, hv_live, hv_013⟩
        ha0 ha13 hu13 hu_e0 hv_e13
  have hFinishClean : ∀ (D : Circuit) (u v : ℕ), Good D u v →
      u < v → gateVal 26 D u e13 = false → gateVal 26 D v e0 = false → False := by
    intro D u v hG huv_lt hu13 hv0
    obtain ⟨hsz, hDAO, hDnd, hDpg, hDdirty,
      hu_lt, hv_lt, _, hnuv, hnvu,
      hu_and, hu_live, hu_013, hu_e0,
      hv_and, hv_live, hv_013, hv_e13⟩ := hG
    have huncov := hUncovOfDirty D hsz hDAO hDpg hDdirty
    have hSubGate : ∀ (k : ℕ) (hk : k < D.gates.length),
        (gateAt D k).op = GateOp.and →
        (26 + k = D.output ∨ InCone 26 D k (D.output - 26)) →
        gateVal 26 D k e013 = true →
        gateVal 26 D k e0 = false →
        gateVal 26 D k e13 = false →
        ((∀ b : Fin 2, wireVal 26 D (opnd D k b) e0 = false) ∨
         (∀ b : Fin 2, wireVal 26 D (opnd D k b) e13 = false)) →
        ∃ a < D.gates.length, InCone 26 D a k ∧ (gateAt D a).op = GateOp.and ∧
          (26 + a = D.output ∨ InCone 26 D a (D.output - 26)) ∧
          gateVal 26 D a e013 = true ∧ gateVal 26 D a e0 = false ∧ gateVal 26 D a e13 = false := by
      intro k hk hk_and hk_live hk013 hk0 hk13 hop_f
      obtain ⟨w0, w1, hwk, hw0_lt, hw1_lt⟩ := isAO2_gate_inputs D hDAO hk
      have hop0 : opnd D k 0 = w0 := by change (gateAt D k).inputs.getD 0 0 = w0; rw [hwk]; rfl
      have hop1 : opnd D k 1 = w1 := by change (gateAt D k).inputs.getD 1 0 = w1; rw [hwk]; rfl
      have hw013 : wireVal 26 D w0 e013 = true ∧ wireVal 26 D w1 e013 = true := by
        have h := hk013
        change wireVal 26 D (26 + k) e013 = true at h
        rw [wireVal_and_pair D hDAO.2.1 hk hk_and hwk e013, Bool.and_eq_true] at h
        exact h
      have hw_ex : ∃ w ∈ (gateAt D k).inputs, w < 26 + k ∧
          wireVal 26 D w e013 = true ∧ wireVal 26 D w e0 = false ∧ wireVal 26 D w e13 = false := by
        rcases hop_f with h0all | h13all
        · have hw0_0 : wireVal 26 D w0 e0 = false := by rw [← hop0]; exact h0all 0
          have hw1_0 : wireVal 26 D w1 e0 = false := by rw [← hop1]; exact h0all 1
          have h13 := hk13
          change wireVal 26 D (26 + k) e13 = false at h13
          rw [wireVal_and_pair D hDAO.2.1 hk hk_and hwk e13, Bool.and_eq_false_iff] at h13
          rcases h13 with h0f | h1f
          · exact ⟨w0, by rw [hwk]; exact List.mem_cons_self, hw0_lt, hw013.1, hw0_0, h0f⟩
          · exact ⟨w1, by rw [hwk]; exact List.mem_cons_of_mem _ List.mem_cons_self, hw1_lt, hw013.2, hw1_0, h1f⟩
        · have hw0_13 : wireVal 26 D w0 e13 = false := by rw [← hop0]; exact h13all 0
          have hw1_13 : wireVal 26 D w1 e13 = false := by rw [← hop1]; exact h13all 1
          have h0 := hk0
          change wireVal 26 D (26 + k) e0 = false at h0
          rw [wireVal_and_pair D hDAO.2.1 hk hk_and hwk e0, Bool.and_eq_false_iff] at h0
          rcases h0 with h0f | h1f
          · exact ⟨w0, by rw [hwk]; exact List.mem_cons_self, hw0_lt, hw013.1, h0f, hw0_13⟩
          · exact ⟨w1, by rw [hwk]; exact List.mem_cons_of_mem _ List.mem_cons_self, hw1_lt, hw013.2, h1f, hw1_13⟩
      obtain ⟨w, hw_mem, hw_lt, hw013_t, hw0_f, hw13_f⟩ := hw_ex
      obtain ⟨a, ha_lt, ha_pos, ha_and, ha013, ha0, ha13⟩ :=
        find_and_in_cone D hDAO w (by omega) hw013_t hw0_f hw13_f
      have hIn : InCone 26 D a k := by
        rw [inCone_iff D a k hk]
        rcases ha_pos with hEq | ⟨hw26, hInw⟩
        · exact ⟨w, hw_mem, by omega, hw_lt, Or.inl (by omega)⟩
        · exact ⟨w, hw_mem, hw26, hw_lt, Or.inr hInw⟩
      have ha_live : 26 + a = D.output ∨ InCone 26 D a (D.output - 26) := by
        rcases hk_live with hEq | hOutk
        · exact Or.inr (by rw [← hEq, Nat.add_sub_cancel_left]; exact hIn)
        · exact Or.inr (inCone_trans D (D.output - 26) a k hIn hOutk)
      exact ⟨a, ha_lt, hIn, ha_and, ha_live, ha013, ha0, ha13⟩
    have hu0 : gateVal 26 D u e0 = false := by
      obtain ⟨w0, w1, hwu, _, _⟩ := isAO2_gate_inputs D hDAO hu_lt
      have hop0 : opnd D u 0 = w0 := by change (gateAt D u).inputs.getD 0 0 = w0; rw [hwu]; rfl
      change wireVal 26 D (26 + u) e0 = false
      rw [wireVal_and_pair D hDAO.2.1 hu_lt hu_and hwu e0, ← hop0, hu_e0 0]
      rfl
    have hv13 : gateVal 26 D v e13 = false := by
      obtain ⟨w0, w1, hwv, _, _⟩ := isAO2_gate_inputs D hDAO hv_lt
      have hop0 : opnd D v 0 = w0 := by change (gateAt D v).inputs.getD 0 0 = w0; rw [hwv]; rfl
      change wireVal 26 D (26 + v) e13 = false
      rw [wireVal_and_pair D hDAO.2.1 hv_lt hv_and hwv e13, ← hop0, hv_e13 0]
      rfl
    obtain ⟨a, ha_lt, hInu, ha_and, ha_live, ha013, ha0, ha13⟩ :=
      hSubGate u hu_lt hu_and hu_live hu_013 hu0 hu13 (Or.inl hu_e0)
    obtain ⟨b, hb_lt, hInv, hb_and, hb_live, hb013, hb0, hb13⟩ :=
      hSubGate v hv_lt hv_and hv_live hv_013 hv0 hv13 (Or.inr hv_e13)
    obtain ⟨d, hd_lt, hd_and, yd, hdy_t, hD_yd_f⟩ := hDdirty
    have hDdirty' : ∃ d : ℕ, PEqualNP.ReadTwo.isAnd D d ∧
        ∃ y : Fin 26 → Bool, gateVal 26 D d y = true ∧ D.eval (List.ofFn y) = false :=
      ⟨d, ⟨hd_lt, hd_and⟩, yd, hdy_t, hD_yd_f⟩
    have hDpgS : ∀ x : Fin 26 → Bool, D.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 13, p - l ∈ ({(0 : Fin 13), 1, 3, 9} : Finset (Fin 13)) ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
      intro x; rw [hDpg x]
      constructor
      · rintro ⟨p, l, h, hp, hl⟩; exact ⟨p, l, (hpg_sub_iff p l).mpr h, hp, hl⟩
      · rintro ⟨p, l, h, hp, hl⟩; exact ⟨p, l, (hpg_sub_iff p l).mp h, hp, hl⟩
    obtain ⟨pu, lu, hpulu, huncov_body⟩ := huncov
    have huncovS : ∃ p l : Fin 13, p - l ∈ ({(0 : Fin 13), 1, 3, 9} : Finset (Fin 13)) ∧
        ¬ ∃ k u v : ℕ, andOn D k u v ∧ orp D 26 (26 + k) D.output ∧
          orp D 26 p.val u ∧ orp D 26 (13 + l.val) v :=
      ⟨pu, lu, (hpg_sub_iff pu lu).mpr hpulu, huncov_body⟩
    by_cases h63 : D.size ≤ 63
    · exact hLe63Clean D h63 hDAO hDnd hDpgS huncovS hDdirty' a b u v huv_lt hnuv hnvu
        ⟨hInu, ⟨ha_lt, ha_and⟩, ⟨hu_lt, hu_and⟩, hu_live, ha013, ha0, ha13, hu_013, hu13, hu_e0⟩
        ⟨hInv, ⟨hb_lt, hb_and⟩, ⟨hv_lt, hv_and⟩, hv_live, hb013, hb13, hb0, hv_013, hv0, hv_e13⟩
    · have h64 : D.size = 64 := by omega
      exact hEq64Clean D h64 hDAO hDnd hDpgS huncovS hDdirty' a b u v huv_lt hnuv hnvu
        ⟨hInu, ⟨ha_lt, ha_and⟩, ⟨hu_lt, hu_and⟩, hu_live, ha013, ha0, ha13, hu_013, hu13, hu_e0⟩
        ⟨hInv, ⟨hb_lt, hb_and⟩, ⟨hv_lt, hv_and⟩, hv_live, hb013, hb13, hb0, hv_013, hv0, hv_e13⟩
  cases hi13 : gateVal 26 C i e13 with
  | true =>
    exact hFinishUnit C i j hGood0 hi13
  | false =>
    cases hj0 : gateVal 26 C j e0 with
    | true =>
      obtain ⟨hGd, hj13', _⟩ := hGoodDual C i j hGood0
      rw [hj0] at hj13'
      exact hFinishUnit (dualCirc C) j i hGd hj13'
    | false =>
      by_cases hlt : i < j
      · exact hFinishClean C i j hGood0 hlt hi13 hj0
      · have hjlt : j < i := by omega
        obtain ⟨hGd, hj13', hi0'⟩ := hGoodDual C i j hGood0
        rw [hj0] at hj13'
        rw [hi13] at hi0'
        exact hFinishClean (dualCirc C) j i hGd hjlt hj13' hi0'
