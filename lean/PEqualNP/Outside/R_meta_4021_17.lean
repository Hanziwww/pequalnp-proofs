import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_4021_17
    (hOneHotAnd0 :
      let shifts : Finset (Fin 13) := {0, 1, 3, 9}
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        C.size ≤ 64 → PEqualNP.TopForm.IsAO2 26 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
        (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 13, p - l ∈ shifts ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
        0 < PEqualNP.TopForm.andPairs 26 C →
        (∃ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ x : Fin 26 → Bool, (C.wires (List.ofFn x)).getD (26 + k) false = true ∧ C.eval (List.ofFn x) = false) →
        (∃ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (C.wires (List.ofFn fun i : Fin 26 => decide (i = 0))).getD (26 + k) false = true) →
        False)
    (hOneSided :
      let shifts : Finset (Fin 13) := {0, 1, 3, 9}
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        C.size ≤ 64 → PEqualNP.TopForm.IsAO2 26 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
        (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 13, p - l ∈ shifts ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
        0 < PEqualNP.TopForm.andPairs 26 C →
        (∃ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ x : Fin 26 → Bool, (C.wires (List.ofFn x)).getD (26 + k) false = true ∧ C.eval (List.ofFn x) = false) →
        let w0 := C.wires (List.ofFn fun i : Fin 26 => decide (i = 0))
        let w13 := C.wires (List.ofFn fun i : Fin 26 => decide (i = 13))
        let w013 := C.wires (List.ofFn fun i : Fin 26 => decide (i = 0 ∨ i = 13))
        (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → w0.getD (26 + k) false = false ∧ w13.getD (26 + k) false = false) →
        (∃ k a b : ℕ, (C.gates[k]? = some (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.and [a, b]) ∨ C.gates[k]? = some (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.and [b, a])) ∧ w0.getD a false = true ∧ w13.getD a false = false ∧ w0.getD b false = false ∧ w13.getD b false = false ∧ w013.getD b false = true) →
        False)
    (hTwoSided :
      let shifts : Finset (Fin 13) := {0, 1, 3, 9}
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        C.size ≤ 64 → PEqualNP.TopForm.IsAO2 26 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
        (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 13, p - l ∈ shifts ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
        0 < PEqualNP.TopForm.andPairs 26 C →
        (∃ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ x : Fin 26 → Bool, (C.wires (List.ofFn x)).getD (26 + k) false = true ∧ C.eval (List.ofFn x) = false) →
        let w0 := C.wires (List.ofFn fun i : Fin 26 => decide (i = 0))
        let w13 := C.wires (List.ofFn fun i : Fin 26 => decide (i = 13))
        let w013 := C.wires (List.ofFn fun i : Fin 26 => decide (i = 0 ∨ i = 13))
        (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → w0.getD (26 + k) false = false ∧ w13.getD (26 + k) false = false) →
        (∃ k a b : ℕ, C.gates[k]? = some (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.and [a, b]) ∧ w0.getD a false = false ∧ w13.getD a false = false ∧ w013.getD a false = true ∧ w0.getD b false = false ∧ w13.getD b false = false ∧ w013.getD b false = true) →
        False) :
    have x1 : PEqualNP.CircuitLowerBounds.Circuit → Fin (26 : ℕ) → ℕ → ℕ → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ)) (x3 x4 : ℕ) => ∃ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate) (x7 : ℕ), x4 = (26 : ℕ) + x5 ∧ x1.gates[x5]? = Option.some x6 ∧ (x6.inputs = [x3, x7] ∨ x6.inputs = [x7, x3]) ∧ (x6.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = x2))).getD x7 Bool.false = Bool.true); have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => x3.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧ (∀ x4 ∈ x3.gates, x4.inputs.Nodup) ∧ (∀ (x4 : Fin (26 : ℕ) → Bool), x3.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), x5 - x6 ∈ x2 ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) ∧ (0 : ℕ) < PEqualNP.TopForm.andPairs (26 : ℕ) x3 ∧ ∃ x4 < x3.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x5 : Fin (26 : ℕ) → Bool), (x3.wires (List.ofFn x5)).getD ((26 : ℕ) + x4) Bool.false = Bool.true ∧ x3.eval (List.ofFn x5) = Bool.false; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → Relation.ReflTransGen (x1 x4 (0 : Fin (26 : ℕ))) (13 : ℕ) x4.output ∨ Relation.ReflTransGen (x1 x4 (13 : Fin (26 : ℕ))) (0 : ℕ) x4.output := by
  dsimp only
  intro C hgood
  obtain ⟨hsz, hao, hnodup, hPG, hap, hdirty⟩ := hgood
  let shifts : Finset (Fin 13) := {0, 1, 3, 9}
  let stepRel : Circuit → Fin 26 → ℕ → ℕ → Prop := fun D v u w =>
    ∃ k g other, w = 26 + k ∧ D.gates[k]? = some g ∧ (g.inputs = [u, other] ∨ g.inputs = [other, u]) ∧
      (g.op = GateOp.or ∨ g.op = GateOp.and ∧ (D.wires (List.ofFn fun i : Fin 26 => decide (i = v))).getD other false = true)
  let R13 : ℕ → Prop := Relation.ReflTransGen (stepRel C 0) 13
  let R0 : ℕ → Prop := Relation.ReflTransGen (stepRel C 13) 0
  change R13 C.output ∨ R0 C.output
  by_contra hneither
  have hn13_out : ¬ R13 C.output := fun h => hneither (Or.inl h)
  have hn0_out : ¬ R0 C.output := fun h => hneither (Or.inr h)
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
  have getD_snoc_eq {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]
  have getD_snoc_ne {α : Type} (l : List α) (a d : α) (j : ℕ) (hj : j ≠ l.length) :
      (l ++ [a]).getD j d = l.getD j d := by
    by_cases hlt : j < l.length
    · exact List.getD_append _ _ _ _ hlt
    · rw [List.getD_eq_default (l ++ [a]) d (n := j) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
          List.getD_eq_default l d (n := j) (by omega)]
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
  have run_append (gs1 gs2 : List Gate) (w : List Bool) :
      run (gs1 ++ gs2) w = run gs2 (run gs1 w) := by
    dsimp only [run]
    exact List.foldl_append
  have wire_gate_eval (x : Fin 26 → Bool) (k : ℕ) (hk : k < C.gates.length) :
      let g := C.gates[k]'hk
      (C.wires (List.ofFn x)).getD (26 + k) false =
        g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) := by
    dsimp only
    let pre := C.gates.take k
    let g := C.gates[k]'hk
    let post := C.gates.drop (k + 1)
    have hsplit : C.gates = pre ++ (g :: post) := by
      have h1 : C.gates.take k ++ C.gates.drop k = C.gates := List.take_append_drop k C.gates
      have h2 : C.gates.drop k = g :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk
      rw [← h2]; exact h1.symm
    have hpre_len : pre.length = k := by simp only [pre, List.length_take]; omega
    have hpre_wlen : (run pre (List.ofFn x)).length = 26 + k := by
      rw [run_len, List.length_ofFn, hpre_len]
    have hrun_eq : C.wires (List.ofFn x) = run post (step (run pre (List.ofFn x)) g) := by
      change run C.gates (List.ofFn x) = _
      conv_lhs => rw [hsplit]
      rw [run_append]
      rfl
    have hrb : ∀ i ∈ g.inputs, i < 26 + k := by
      intro i hi
      have h1 := hao.2.1 k hk i
      have hga : gateAt C k = g := by
        change C.gates.getD k ⟨GateOp.or, []⟩ = C.gates[k]'hk
        exact List.getD_eq_getElem C.gates ⟨GateOp.or, []⟩ hk
      rw [hga] at h1
      exact h1 hi
    have hstep_len : (step (run pre (List.ofFn x)) g).length = 26 + k + 1 := by
      simp only [step, List.length_append, hpre_wlen, List.length_cons, List.length_nil]
    have hkeep_k : (C.wires (List.ofFn x)).getD (26 + k) false =
        g.op.eval (g.inputs.map fun i => (run pre (List.ofFn x)).getD i false) := by
      rw [hrun_eq, run_keep post _ (26 + k) (by omega)]
      dsimp only [step]
      simpa only [hpre_wlen] using getD_snoc_eq (run pre (List.ofFn x))
        (g.op.eval (g.inputs.map fun i => (run pre (List.ofFn x)).getD i false)) false
    rw [hkeep_k]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hilt : i < 26 + k := hrb i hi
    rw [hrun_eq, run_keep post _ i (by omega), getD_snoc_ne (run pre (List.ofFn x)) _ false i (by omega)]
  let dualIdx : Fin 26 → Fin 26 := fun i =>
    if h : i.val < 13 then Fin.natAdd 13 (-(⟨i.val, h⟩ : Fin 13))
    else Fin.castAdd 13 (-(⟨i.val - 13, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt h) i.isLt⟩ : Fin 13))
  have hdualIdx_inv : ∀ i : Fin 26, dualIdx (dualIdx i) = i := by dsimp only [dualIdx]; decide
  have hdualIdx_0 : dualIdx 0 = 13 := by dsimp only [dualIdx]; decide
  have hdualIdx_13 : dualIdx 13 = 0 := by dsimp only [dualIdx]; decide
  have hdualIdx_cast : ∀ p : Fin 13, dualIdx (Fin.castAdd 13 p) = Fin.natAdd 13 (-p) := by dsimp only [dualIdx]; decide
  have hdualIdx_nat : ∀ l : Fin 13, dualIdx (Fin.natAdd 13 l) = Fin.castAdd 13 (-l) := by dsimp only [dualIdx]; decide
  have hneg_sub : ∀ p l : Fin 13, (-l) - (-p) = p - l := by decide
  let dualWire : ℕ → ℕ := fun w => if h : w < 26 then (dualIdx ⟨w, h⟩).val else w
  have hdualWire_lt (w : ℕ) (hw : w < 26) : dualWire w < 26 := by
    simp only [dualWire, hw, ↓reduceDIte]
    exact (dualIdx ⟨w, hw⟩).isLt
  have hdualWire_ge (w : ℕ) (hw : 26 ≤ w) : dualWire w = w := by
    have hn : ¬ w < 26 := by omega
    simp only [dualWire, hn, ↓reduceDIte]
  have hdualWire_inv (w : ℕ) : dualWire (dualWire w) = w := by
    by_cases hw : w < 26
    · simp only [dualWire, hw, (dualIdx ⟨w, hw⟩).isLt, ↓reduceDIte]
      have h2 := hdualIdx_inv ⟨w, hw⟩
      exact congrArg Fin.val h2
    · have hge : 26 ≤ w := by omega
      rw [hdualWire_ge w hge, hdualWire_ge w hge]
  have hdualWire_inj : Function.Injective dualWire := fun a b hab => by
    have := congrArg dualWire hab
    rw [hdualWire_inv a, hdualWire_inv b] at this
    exact this
  let dualC : Circuit := ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map dualWire⟩), dualWire C.output⟩
  have remap_bijection (gs : List Gate) (wA wB : List Bool)
      (hlen_w : wA.length = wB.length) (h26 : 26 ≤ wA.length)
      (hrel : ∀ i, wB.getD (dualWire i) false = wA.getD i false) :
      ∀ i, (run (gs.map fun g => ⟨g.op, g.inputs.map dualWire⟩) wB).getD (dualWire i) false =
        (run gs wA).getD i false := by
    induction gs generalizing wA wB with
    | nil => exact hrel
    | cons g rest ih =>
      simp only [List.map_cons, run, List.foldl_cons] at ih ⊢
      have hinp : (g.inputs.map dualWire).map (fun i => wB.getD i false) =
          g.inputs.map (fun i => wA.getD i false) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro i _
        exact hrel i
      let b := g.op.eval (g.inputs.map fun i => wA.getD i false)
      have hstepB : step wB ⟨g.op, g.inputs.map dualWire⟩ = wB ++ [b] := by
        dsimp only [step, b]; rw [hinp]
      rw [hstepB]
      apply ih (step wA g) (wB ++ [b])
      · simp only [step, List.length_append, hlen_w, List.length_cons, List.length_nil]
      · simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
      · intro i
        dsimp only [step]
        by_cases hi : i = wA.length
        · subst hi
          have hfi : dualWire wA.length = wB.length := by rw [hdualWire_ge wA.length h26, hlen_w]
          rw [hfi, getD_snoc_eq wB b false, getD_snoc_eq wA b false]
        · have hfi : dualWire i ≠ wB.length := by
            intro hfeq
            by_cases hlt : i < 26
            · have := hdualWire_lt i hlt; omega
            · have := hdualWire_ge i (by omega); omega
          rw [getD_snoc_ne wB b false (dualWire i) hfi, getD_snoc_ne wA b false i hi]
          exact hrel i
  have hdual_wires (x : Fin 26 → Bool) (w : ℕ) :
      (dualC.wires (List.ofFn x)).getD (dualWire w) false =
        (C.wires (List.ofFn fun i : Fin 26 => x (dualIdx i))).getD w false := by
    let y : Fin 26 → Bool := fun i => x (dualIdx i)
    have hrel0 : ∀ i, (List.ofFn x).getD (dualWire i) false = (List.ofFn y).getD i false := by
      intro i
      by_cases hi : i < 26
      · have hdi := hdualWire_lt i hi
        have hlenx : dualWire i < (List.ofFn x).length := by rw [List.length_ofFn]; exact hdi
        have hleny : i < (List.ofFn y).length := by rw [List.length_ofFn]; exact hi
        rw [List.getD_eq_getElem _ _ hlenx, List.getElem_ofFn, List.getD_eq_getElem _ _ hleny, List.getElem_ofFn]
        dsimp only [y, dualWire]
        simp only [hi, ↓reduceDIte]
      · have hge : 26 ≤ i := by omega
        rw [hdualWire_ge i hge,
            List.getD_eq_default (List.ofFn x) false (n := i) (by rw [List.length_ofFn]; exact hge),
            List.getD_eq_default (List.ofFn y) false (n := i) (by rw [List.length_ofFn]; exact hge)]
    exact remap_bijection C.gates (List.ofFn y) (List.ofFn x)
      (by simp only [List.length_ofFn]) (by simp only [List.length_ofFn]; omega) hrel0 w
  have hdual_eval (x : Fin 26 → Bool) :
      dualC.eval (List.ofFn x) = C.eval (List.ofFn fun i : Fin 26 => x (dualIdx i)) :=
    hdual_wires x C.output
  have hdual_sz : dualC.size ≤ 64 := by
    change (C.gates.map _).length ≤ 64
    rw [List.length_map]
    exact hsz
  have hdual_gateAt_op (j : ℕ) : (gateAt dualC j).op = (gateAt C j).op := by
    change ((C.gates.map (fun g => Gate.mk g.op (g.inputs.map dualWire))).getD j (Gate.mk GateOp.or [])).op =
      (C.gates.getD j (Gate.mk GateOp.or [])).op
    by_cases hj : j < C.gates.length
    · rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj),
          List.getElem_map, List.getD_eq_getElem _ _ hj]
    · rw [List.getD_eq_default _ _ (n := j) (by rw [List.length_map]; omega),
          List.getD_eq_default _ _ (n := j) (by omega)]
  have hdual_ao : IsAO2 26 dualC := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simp only [dualC, List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      exact hao.1 g0 hg0
    · intro j hj i hi
      have hj' : j < C.gates.length := by
        simp only [dualC, List.length_map] at hj; exact hj
      have hga_d : gateAt dualC j = Gate.mk (C.gates[j]'hj').op ((C.gates[j]'hj').inputs.map dualWire) := by
        change (C.gates.map (fun g => Gate.mk g.op (g.inputs.map dualWire))).getD j (Gate.mk GateOp.or []) = _
        rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj'), List.getElem_map]
      have hga_c : gateAt C j = C.gates[j]'hj' := by
        change C.gates.getD j (Gate.mk GateOp.or []) = _
        exact List.getD_eq_getElem _ _ hj'
      rw [hga_d] at hi
      simp only [List.mem_map] at hi
      obtain ⟨i0, hi0, rfl⟩ := hi
      have hi0_lt : i0 < 26 + j := by
        have hrb := hao.2.1 j hj' i0
        rw [hga_c] at hrb
        exact hrb hi0
      by_cases hlt : i0 < 26
      · have := hdualWire_lt i0 hlt; omega
      · rw [hdualWire_ge i0 (by omega)]; exact hi0_lt
    · intro g hg
      simp only [dualC, List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      rw [List.length_map]
      exact hao.2.2 g0 hg0
  have hdual_nodup : ∀ g ∈ dualC.gates, g.inputs.Nodup := by
    intro g hg
    simp only [dualC, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    exact (hnodup g0 hg0).map hdualWire_inj
  have hdual_PG (x : Fin 26 → Bool) :
      dualC.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 13, p - l ∈ shifts ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
    rw [hdual_eval x, hPG]
    constructor
    · intro h
      obtain ⟨p, l, hpl, hp, hl⟩ := h
      rw [hdualIdx_cast p] at hp
      rw [hdualIdx_nat l] at hl
      exact ⟨-l, -p, by rw [hneg_sub p l]; exact hpl, hl, hp⟩
    · intro h
      obtain ⟨p, l, hpl, hp, hl⟩ := h
      refine ⟨-l, -p, by rw [hneg_sub p l]; exact hpl, ?_, ?_⟩
      · rw [hdualIdx_cast (-l), neg_neg]; exact hl
      · rw [hdualIdx_nat (-p), neg_neg]; exact hp
  have hfilter_dual (m : ℕ) (l : List ℕ) :
      (l.map dualWire).filter (fun w => decide (26 ≤ w ∧ w < 26 + m)) =
        l.filter (fun w => decide (26 ≤ w ∧ w < 26 + m)) := by
    induction l with
    | nil => rfl
    | cons a t ih =>
      simp only [List.map_cons, List.filter_cons]
      by_cases ha : a < 26
      · have hda := hdualWire_lt a ha
        have h1 : decide (26 ≤ dualWire a ∧ dualWire a < 26 + m) = false := by
          simp only [decide_eq_false_iff_not]; omega
        have h2 : decide (26 ≤ a ∧ a < 26 + m) = false := by
          simp only [decide_eq_false_iff_not]; omega
        rw [h1, h2]
        exact ih
      · rw [hdualWire_ge a (by omega)]
        cases decide (26 ≤ a ∧ a < 26 + m) <;> simp only [ih]
  have hcones_fold (gs : List Gate) (cs : List (List ℕ)) :
      (gs.map (fun g => ⟨g.op, g.inputs.map dualWire⟩)).foldl (coneStep 26) cs =
        gs.foldl (coneStep 26) cs := by
    induction gs generalizing cs with
    | nil => rfl
    | cons g rest ih =>
      simp only [List.map_cons, List.foldl_cons]
      have hstep_eq : coneStep 26 cs ⟨g.op, g.inputs.map dualWire⟩ = coneStep 26 cs g := by
        change cs ++ [((g.inputs.map dualWire).filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap
            (fun w => (w - 26) :: cs.getD (w - 26) [])] =
          cs ++ [(g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap
            (fun w => (w - 26) :: cs.getD (w - 26) [])]
        rw [hfilter_dual cs.length g.inputs]
      rw [hstep_eq]
      exact ih (coneStep 26 cs g)
  have hdual_cones : cones 26 dualC = cones 26 C := hcones_fold C.gates []
  have hdual_ap : 0 < andPairs 26 dualC := by
    have heq : andPairs 26 dualC = andPairs 26 C := by
      let _ := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
      change ((Finset.range dualC.gates.length ×ˢ Finset.range dualC.gates.length).filter
          (fun p : ℕ × ℕ => (gateAt dualC p.1).op = GateOp.and ∧ (gateAt dualC p.2).op = GateOp.and ∧ InCone 26 dualC p.1 p.2)).card =
        ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
          (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧ (gateAt C p.2).op = GateOp.and ∧ InCone 26 C p.1 p.2)).card
      have hlen_d : dualC.gates.length = C.gates.length := List.length_map _
      rw [hlen_d]
      congr 1
      apply Finset.filter_congr
      intro p _
      have hic : InCone 26 dualC p.1 p.2 ↔ InCone 26 C p.1 p.2 := by
        change (p.1 ∈ (cones 26 dualC).getD p.2 []) ↔ (p.1 ∈ (cones 26 C).getD p.2 [])
        rw [hdual_cones]
      rw [hdual_gateAt_op p.1, hdual_gateAt_op p.2, hic]
    rw [heq]
    exact hap
  have hdual_dirty : ∃ k < dualC.gates.length, (gateAt dualC k).op = GateOp.and ∧
      ∃ x : Fin 26 → Bool, (dualC.wires (List.ofFn x)).getD (26 + k) false = true ∧ dualC.eval (List.ofFn x) = false := by
    obtain ⟨k, hk, hop, x, hwk, hev⟩ := hdirty
    refine ⟨k, by simp only [dualC, List.length_map]; exact hk, by rw [hdual_gateAt_op k]; exact hop,
      fun i => x (dualIdx i), ?_, ?_⟩
    · have hcomp : (fun i : Fin 26 => x (dualIdx (dualIdx i))) = x := by
        funext i; rw [hdualIdx_inv i]
      have hw := hdual_wires (fun i => x (dualIdx i)) (26 + k)
      rw [hdualWire_ge (26 + k) (by omega), hcomp] at hw
      rw [hw]; exact hwk
    · have hcomp : (fun i : Fin 26 => x (dualIdx (dualIdx i))) = x := by
        funext i; rw [hdualIdx_inv i]
      rw [hdual_eval, hcomp]; exact hev
  let w0 := C.wires (List.ofFn fun i : Fin 26 => decide (i = 0))
  let w13 := C.wires (List.ofFn fun i : Fin 26 => decide (i = 13))
  let w013 := C.wires (List.ofFn fun i : Fin 26 => decide (i = 0 ∨ i = 13))
  let dw0 := dualC.wires (List.ofFn fun i : Fin 26 => decide (i = 0))
  let dw13 := dualC.wires (List.ofFn fun i : Fin 26 => decide (i = 13))
  let dw013 := dualC.wires (List.ofFn fun i : Fin 26 => decide (i = 0 ∨ i = 13))
  have hdw0 (w : ℕ) : dw0.getD (dualWire w) false = w13.getD w false := by
    have hfun : (fun i : Fin 26 => decide (dualIdx i = 0)) = (fun i : Fin 26 => decide (i = 13)) := by
      funext i
      rw [decide_eq_decide]
      exact ⟨fun h => by rw [← hdualIdx_inv i, h, hdualIdx_0], fun h => by rw [h, hdualIdx_13]⟩
    have h := hdual_wires (fun i : Fin 26 => decide (i = 0)) w
    rw [hfun] at h
    exact h
  have hdw13 (w : ℕ) : dw13.getD (dualWire w) false = w0.getD w false := by
    have hfun : (fun i : Fin 26 => decide (dualIdx i = 13)) = (fun i : Fin 26 => decide (i = 0)) := by
      funext i
      rw [decide_eq_decide]
      exact ⟨fun h => by rw [← hdualIdx_inv i, h, hdualIdx_13], fun h => by rw [h, hdualIdx_0]⟩
    have h := hdual_wires (fun i : Fin 26 => decide (i = 13)) w
    rw [hfun] at h
    exact h
  have hdw013 (w : ℕ) : dw013.getD (dualWire w) false = w013.getD w false := by
    have hfun : (fun i : Fin 26 => decide (dualIdx i = 0 ∨ dualIdx i = 13)) =
        (fun i : Fin 26 => decide (i = 0 ∨ i = 13)) := by
      funext i
      rw [decide_eq_decide]
      constructor
      · intro h; rcases h with h0 | h13
        · exact Or.inr (by rw [← hdualIdx_inv i, h0, hdualIdx_0])
        · exact Or.inl (by rw [← hdualIdx_inv i, h13, hdualIdx_13])
      · intro h; rcases h with h0 | h13
        · exact Or.inr (by rw [h0, hdualIdx_0])
        · exact Or.inl (by rw [h13, hdualIdx_13])
    have h := hdual_wires (fun i : Fin 26 => decide (i = 0 ∨ i = 13)) w
    rw [hfun] at h
    exact h
  have hNo0 (k : ℕ) (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.and) :
      w0.getD (26 + k) false = false := by
    cases h : w0.getD (26 + k) false with
    | false => rfl
    | true => exact False.elim (hOneHotAnd0 C hsz hao hnodup hPG hap hdirty ⟨k, hk, hop, h⟩)
  have hNo13 (k : ℕ) (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.and) :
      w13.getD (26 + k) false = false := by
    cases h : w13.getD (26 + k) false with
    | false => rfl
    | true =>
      have hdk : dw0.getD (26 + k) false = true := by
        have := hdw0 (26 + k)
        rw [hdualWire_ge (26 + k) (by omega)] at this
        rw [this]; exact h
      exact False.elim (hOneHotAnd0 dualC hdual_sz hdual_ao hdual_nodup hdual_PG hdual_ap hdual_dirty
        ⟨k, by simp only [dualC, List.length_map]; exact hk, by rw [hdual_gateAt_op k]; exact hop, hdk⟩)
  have hNoBoth (k : ℕ) (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.and) :
      w0.getD (26 + k) false = false ∧ w13.getD (26 + k) false = false :=
    ⟨hNo0 k hk hop, hNo13 k hk hop⟩
  have hDualNoBoth (k : ℕ) (hk : k < dualC.gates.length) (hop : (gateAt dualC k).op = GateOp.and) :
      dw0.getD (26 + k) false = false ∧ dw13.getD (26 + k) false = false := by
    have hk' : k < C.gates.length := by simp only [dualC, List.length_map] at hk; exact hk
    have hop' : (gateAt C k).op = GateOp.and := by rw [← hdual_gateAt_op k]; exact hop
    have h0 := hdw0 (26 + k)
    have h13 := hdw13 (26 + k)
    rw [hdualWire_ge (26 + k) (by omega)] at h0 h13
    rw [h0, h13]
    exact ⟨hNo13 k hk' hop', hNo0 k hk' hop'⟩
  have hreach0 : ∀ w < 26 + C.gates.length, w0.getD w false = true → R0 w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hwt
      by_cases hw26 : w < 26
      · have hinit : w0.getD w false = decide ((⟨w, hw26⟩ : Fin 26) = 0) := by
          dsimp only [w0]
          change (run C.gates (List.ofFn fun i : Fin 26 => decide (i = 0))).getD w false = _
          rw [run_keep C.gates _ w (by rw [List.length_ofFn]; exact hw26),
              List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hw26), List.getElem_ofFn]
        rw [hinit, decide_eq_true_eq] at hwt
        have hw0 : w = 0 := congrArg Fin.val hwt
        subst hw0
        exact Relation.ReflTransGen.refl
      · let k := w - 26
        have hw_eq : w = 26 + k := by omega
        have hk : k < C.gates.length := by omega
        let g := C.gates[k]'hk
        have hg_mem : g ∈ C.gates := List.getElem_mem hk
        have hg_len : g.inputs.length = 2 := hao.2.2 g hg_mem
        have hga : gateAt C k = g := by
          change C.gates.getD k ⟨GateOp.or, []⟩ = _; exact List.getD_eq_getElem _ _ hk
        have hgop : g.op = GateOp.or := by
          rcases hao.1 g hg_mem with hop | hop
          · have h0 := hNo0 k hk (by rw [hga]; exact hop)
            rw [hw_eq] at hwt
            rw [h0] at hwt
            cases hwt
          · exact hop
        cases hgi : g.inputs with
        | nil => rw [hgi] at hg_len; cases hg_len
        | cons a t1 =>
          cases t1 with
          | nil => rw [hgi] at hg_len; cases hg_len
          | cons b t2 =>
            cases t2 with
            | cons _ _ => rw [hgi] at hg_len; cases hg_len
            | nil =>
              have ha_lt : a < w := by
                have hrb := hao.2.1 k hk a
                rw [hga, hgi] at hrb
                have := hrb (by simp only [List.mem_cons, true_or])
                omega
              have hb_lt : b < w := by
                have hrb := hao.2.1 k hk b
                rw [hga, hgi] at hrb
                have := hrb (by simp only [List.mem_cons, true_or, or_true])
                omega
              have hev := wire_gate_eval (fun i : Fin 26 => decide (i = 0)) k hk
              change w0.getD (26 + k) false = g.op.eval (g.inputs.map fun i => w0.getD i false) at hev
              rw [hw_eq, hev, hgop, hgi] at hwt
              change (w0.getD a false || (w0.getD b false || false)) = true at hwt
              rw [Bool.or_false, Bool.or_eq_true] at hwt
              rcases hwt with hat | hbt
              · exact Relation.ReflTransGen.tail (ih a ha_lt (by omega) hat)
                  ⟨k, g, b, hw_eq, List.getElem?_eq_getElem hk, Or.inl hgi, Or.inl hgop⟩
              · exact Relation.ReflTransGen.tail (ih b hb_lt (by omega) hbt)
                  ⟨k, g, a, hw_eq, List.getElem?_eq_getElem hk, Or.inr hgi, Or.inl hgop⟩
  have hreach13 : ∀ w < 26 + C.gates.length, w13.getD w false = true → R13 w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hwt
      by_cases hw26 : w < 26
      · have hinit : w13.getD w false = decide ((⟨w, hw26⟩ : Fin 26) = 13) := by
          dsimp only [w13]
          change (run C.gates (List.ofFn fun i : Fin 26 => decide (i = 13))).getD w false = _
          rw [run_keep C.gates _ w (by rw [List.length_ofFn]; exact hw26),
              List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hw26), List.getElem_ofFn]
        rw [hinit, decide_eq_true_eq] at hwt
        have hw13 : w = 13 := congrArg Fin.val hwt
        subst hw13
        exact Relation.ReflTransGen.refl
      · let k := w - 26
        have hw_eq : w = 26 + k := by omega
        have hk : k < C.gates.length := by omega
        let g := C.gates[k]'hk
        have hg_mem : g ∈ C.gates := List.getElem_mem hk
        have hg_len : g.inputs.length = 2 := hao.2.2 g hg_mem
        have hga : gateAt C k = g := by
          change C.gates.getD k ⟨GateOp.or, []⟩ = _; exact List.getD_eq_getElem _ _ hk
        have hgop : g.op = GateOp.or := by
          rcases hao.1 g hg_mem with hop | hop
          · have h13 := hNo13 k hk (by rw [hga]; exact hop)
            rw [hw_eq] at hwt
            rw [h13] at hwt
            cases hwt
          · exact hop
        cases hgi : g.inputs with
        | nil => rw [hgi] at hg_len; cases hg_len
        | cons a t1 =>
          cases t1 with
          | nil => rw [hgi] at hg_len; cases hg_len
          | cons b t2 =>
            cases t2 with
            | cons _ _ => rw [hgi] at hg_len; cases hg_len
            | nil =>
              have ha_lt : a < w := by
                have hrb := hao.2.1 k hk a
                rw [hga, hgi] at hrb
                have := hrb (by simp only [List.mem_cons, true_or])
                omega
              have hb_lt : b < w := by
                have hrb := hao.2.1 k hk b
                rw [hga, hgi] at hrb
                have := hrb (by simp only [List.mem_cons, true_or, or_true])
                omega
              have hev := wire_gate_eval (fun i : Fin 26 => decide (i = 13)) k hk
              change w13.getD (26 + k) false = g.op.eval (g.inputs.map fun i => w13.getD i false) at hev
              rw [hw_eq, hev, hgop, hgi] at hwt
              change (w13.getD a false || (w13.getD b false || false)) = true at hwt
              rw [Bool.or_false, Bool.or_eq_true] at hwt
              rcases hwt with hat | hbt
              · exact Relation.ReflTransGen.tail (ih a ha_lt (by omega) hat)
                  ⟨k, g, b, hw_eq, List.getElem?_eq_getElem hk, Or.inl hgi, Or.inl hgop⟩
              · exact Relation.ReflTransGen.tail (ih b hb_lt (by omega) hbt)
                  ⟨k, g, a, hw_eq, List.getElem?_eq_getElem hk, Or.inr hgi, Or.inl hgop⟩
  have hmain : ∀ w < 26 + C.gates.length, w013.getD w false = true → ¬ R13 w → ¬ R0 w → False := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hw013 hn13 hn0
      by_cases hw26 : w < 26
      · have hinit : w013.getD w false = decide ((⟨w, hw26⟩ : Fin 26) = 0 ∨ (⟨w, hw26⟩ : Fin 26) = 13) := by
          dsimp only [w013]
          change (run C.gates (List.ofFn fun i : Fin 26 => decide (i = 0 ∨ i = 13))).getD w false = _
          rw [run_keep C.gates _ w (by rw [List.length_ofFn]; exact hw26),
              List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hw26), List.getElem_ofFn]
        rw [hinit, decide_eq_true_eq] at hw013
        rcases hw013 with h0 | h13
        · have hw0 : w = 0 := congrArg Fin.val h0
          subst hw0
          exact hn0 Relation.ReflTransGen.refl
        · have hw13 : w = 13 := congrArg Fin.val h13
          subst hw13
          exact hn13 Relation.ReflTransGen.refl
      · let k := w - 26
        have hw_eq : w = 26 + k := by omega
        have hk : k < C.gates.length := by omega
        let g := C.gates[k]'hk
        have hg_mem : g ∈ C.gates := List.getElem_mem hk
        have hg_len : g.inputs.length = 2 := hao.2.2 g hg_mem
        have hga : gateAt C k = g := by
          change C.gates.getD k ⟨GateOp.or, []⟩ = _; exact List.getD_eq_getElem _ _ hk
        cases hgi : g.inputs with
        | nil => rw [hgi] at hg_len; cases hg_len
        | cons a t1 =>
          cases t1 with
          | nil => rw [hgi] at hg_len; cases hg_len
          | cons b t2 =>
            cases t2 with
            | cons _ _ => rw [hgi] at hg_len; cases hg_len
            | nil =>
              have ha_lt : a < w := by
                have hrb := hao.2.1 k hk a
                rw [hga, hgi] at hrb
                have := hrb (by simp only [List.mem_cons, true_or])
                omega
              have hb_lt : b < w := by
                have hrb := hao.2.1 k hk b
                rw [hga, hgi] at hrb
                have := hrb (by simp only [List.mem_cons, true_or, or_true])
                omega
              have hev013 := wire_gate_eval (fun i : Fin 26 => decide (i = 0 ∨ i = 13)) k hk
              change w013.getD (26 + k) false = g.op.eval (g.inputs.map fun i => w013.getD i false) at hev013
              rcases hao.1 g hg_mem with hgop | hgop
              · rw [hw_eq, hev013, hgop, hgi] at hw013
                change (w013.getD a false && (w013.getD b false && true)) = true at hw013
                rw [Bool.and_true, Bool.and_eq_true] at hw013
                obtain ⟨ha013, hb013⟩ := hw013
                by_cases ha_n : ¬ R13 a ∧ ¬ R0 a
                · exact ih a ha_lt (by omega) ha013 ha_n.1 ha_n.2
                · by_cases hb_n : ¬ R13 b ∧ ¬ R0 b
                  · exact ih b hb_lt (by omega) hb013 hb_n.1 hb_n.2
                  · have haR : R13 a ∨ R0 a := by
                      by_contra h; exact ha_n ⟨fun h1 => h (Or.inl h1), fun h2 => h (Or.inr h2)⟩
                    have hbR : R13 b ∨ R0 b := by
                      by_contra h; exact hb_n ⟨fun h1 => h (Or.inl h1), fun h2 => h (Or.inr h2)⟩
                    have hstep_0_b (ha0 : w0.getD a false = true) (hb13 : R13 b) : False :=
                      hn13 (Relation.ReflTransGen.tail hb13
                        ⟨k, g, a, hw_eq, List.getElem?_eq_getElem hk, Or.inr hgi, Or.inr ⟨hgop, ha0⟩⟩)
                    have hstep_13_b (ha13 : w13.getD a false = true) (hb0 : R0 b) : False :=
                      hn0 (Relation.ReflTransGen.tail hb0
                        ⟨k, g, a, hw_eq, List.getElem?_eq_getElem hk, Or.inr hgi, Or.inr ⟨hgop, ha13⟩⟩)
                    have hstep_0_a (hb0 : w0.getD b false = true) (ha13 : R13 a) : False :=
                      hn13 (Relation.ReflTransGen.tail ha13
                        ⟨k, g, b, hw_eq, List.getElem?_eq_getElem hk, Or.inl hgi, Or.inr ⟨hgop, hb0⟩⟩)
                    have hstep_13_a (hb13 : w13.getD b false = true) (ha0 : R0 a) : False :=
                      hn0 (Relation.ReflTransGen.tail ha0
                        ⟨k, g, b, hw_eq, List.getElem?_eq_getElem hk, Or.inl hgi, Or.inr ⟨hgop, hb13⟩⟩)
                    have hgk_eq : C.gates[k]? = some ⟨GateOp.and, [a, b]⟩ := by
                      rw [List.getElem?_eq_getElem hk]
                      cases hg_mk : g with
                      | mk op ins =>
                        rw [hg_mk] at hgop hgi
                        dsimp only at hgop hgi
                        subst hgop; subst hgi
                        exact congrArg some hg_mk
                    have hdual_gk_eq : dualC.gates[k]? = some ⟨GateOp.and, [dualWire a, dualWire b]⟩ := by
                      have hk_d : k < dualC.gates.length := by simp only [dualC, List.length_map]; exact hk
                      rw [List.getElem?_eq_getElem hk_d]
                      dsimp only [dualC]
                      rw [List.getElem_map]
                      have h1 : C.gates[k]'hk = ⟨GateOp.and, [a, b]⟩ := by
                        have h2 := hgk_eq
                        rw [List.getElem?_eq_getElem hk, Option.some.injEq] at h2
                        exact h2
                      rw [h1]
                      rfl
                    cases ha0 : w0.getD a false with
                    | true =>
                      cases ha13 : w13.getD a false with
                      | true =>
                        rcases hbR with h1 | h2
                        · exact hstep_0_b ha0 h1
                        · exact hstep_13_b ha13 h2
                      | false =>
                        cases hb0 : w0.getD b false with
                        | true =>
                          have hev0 := wire_gate_eval (fun i : Fin 26 => decide (i = 0)) k hk
                          change w0.getD (26 + k) false = g.op.eval (g.inputs.map fun i => w0.getD i false) at hev0
                          rw [hgop, hgi] at hev0
                          change w0.getD (26 + k) false = (w0.getD a false && (w0.getD b false && true)) at hev0
                          rw [ha0, hb0] at hev0
                          have hno := hNo0 k hk (by rw [hga]; exact hgop)
                          rw [hno] at hev0
                          cases hev0
                        | false =>
                          cases hb13 : w13.getD b false with
                          | true => exact hstep_0_b ha0 (hreach13 b (by omega) hb13)
                          | false =>
                            exact hOneSided C hsz hao hnodup hPG hap hdirty hNoBoth
                              ⟨k, a, b, Or.inl hgk_eq, ha0, ha13, hb0, hb13, hb013⟩
                    | false =>
                      cases ha13 : w13.getD a false with
                      | true =>
                        cases hb0 : w0.getD b false with
                        | true => exact hstep_13_b ha13 (hreach0 b (by omega) hb0)
                        | false =>
                          cases hb13 : w13.getD b false with
                          | true =>
                            have hev13 := wire_gate_eval (fun i : Fin 26 => decide (i = 13)) k hk
                            change w13.getD (26 + k) false = g.op.eval (g.inputs.map fun i => w13.getD i false) at hev13
                            rw [hgop, hgi] at hev13
                            change w13.getD (26 + k) false = (w13.getD a false && (w13.getD b false && true)) at hev13
                            rw [ha13, hb13] at hev13
                            have hno := hNo13 k hk (by rw [hga]; exact hgop)
                            rw [hno] at hev13
                            cases hev13
                          | false =>
                            exact hOneSided dualC hdual_sz hdual_ao hdual_nodup hdual_PG hdual_ap hdual_dirty hDualNoBoth
                              ⟨k, dualWire a, dualWire b, Or.inl hdual_gk_eq,
                               by rw [hdw0 a]; exact ha13, by rw [hdw13 a]; exact ha0,
                               by rw [hdw0 b]; exact hb13, by rw [hdw13 b]; exact hb0,
                               by rw [hdw013 b]; exact hb013⟩
                      | false =>
                        cases hb0 : w0.getD b false with
                        | true =>
                          cases hb13 : w13.getD b false with
                          | true =>
                            rcases haR with h1 | h2
                            · exact hstep_0_a hb0 h1
                            · exact hstep_13_a hb13 h2
                          | false =>
                            exact hOneSided C hsz hao hnodup hPG hap hdirty hNoBoth
                              ⟨k, b, a, Or.inr hgk_eq, hb0, hb13, ha0, ha13, ha013⟩
                        | false =>
                          cases hb13 : w13.getD b false with
                          | true =>
                            exact hOneSided dualC hdual_sz hdual_ao hdual_nodup hdual_PG hdual_ap hdual_dirty hDualNoBoth
                              ⟨k, dualWire b, dualWire a, Or.inr hdual_gk_eq,
                               by rw [hdw0 b]; exact hb13, by rw [hdw13 b]; exact hb0,
                               by rw [hdw0 a]; exact ha13, by rw [hdw13 a]; exact ha0,
                               by rw [hdw013 a]; exact ha013⟩
                          | false =>
                            exact hTwoSided C hsz hao hnodup hPG hap hdirty hNoBoth
                              ⟨k, a, b, hgk_eq, ha0, ha13, ha013, hb0, hb13, hb013⟩
              · rw [hw_eq, hev013, hgop, hgi] at hw013
                change (w013.getD a false || (w013.getD b false || false)) = true at hw013
                rw [Bool.or_false, Bool.or_eq_true] at hw013
                rcases hw013 with ha013 | hb013
                · exact ih a ha_lt (by omega) ha013
                    (fun h => hn13 (Relation.ReflTransGen.tail h ⟨k, g, b, hw_eq, List.getElem?_eq_getElem hk, Or.inl hgi, Or.inl hgop⟩))
                    (fun h => hn0 (Relation.ReflTransGen.tail h ⟨k, g, b, hw_eq, List.getElem?_eq_getElem hk, Or.inl hgi, Or.inl hgop⟩))
                · exact ih b hb_lt (by omega) hb013
                    (fun h => hn13 (Relation.ReflTransGen.tail h ⟨k, g, a, hw_eq, List.getElem?_eq_getElem hk, Or.inr hgi, Or.inl hgop⟩))
                    (fun h => hn0 (Relation.ReflTransGen.tail h ⟨k, g, a, hw_eq, List.getElem?_eq_getElem hk, Or.inr hgi, Or.inl hgop⟩))
  have hw013_out : w013.getD C.output false = true := by
    change C.eval (List.ofFn fun i : Fin 26 => decide (i = 0 ∨ i = 13)) = true
    rw [hPG]
    exact ⟨0, 0, by decide, by decide, by decide⟩
  have hout_lt : C.output < 26 + C.gates.length := by
    by_contra hge
    have hlen_w : w013.length = 26 + C.gates.length := by
      change (run C.gates (List.ofFn fun i : Fin 26 => decide (i = 0 ∨ i = 13))).length = _
      rw [run_len, List.length_ofFn]
    rw [List.getD_eq_default w013 false (n := C.output) (by omega)] at hw013_out
    cases hw013_out
  exact hmain C.output hout_lt hw013_out hn13_out hn0_out
