import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_5176_17
    (hSize63Same :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        C.size = 63 →
        PEqualNP.TopForm.IsAO2 26 C →
        (∀ g ∈ C.gates, g.inputs.Nodup) →
        (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
            x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
        have ev : ℕ → ℕ → Bool := fun m w => (C.wires (List.ofFn fun i : Fin 26 => m.testBit i.val)).getD w false
        ∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
          C.gates[k]? = some g →
          g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ev 8193 (26 + k) = true →
          (∀ u ∈ g.inputs, ev 1 u = false ∧ ev 8192 u = false) →
          ev 8191 (26 + k) = false →
          ev 25018369 (26 + k) = false →
          ev 67100672 (26 + k) = false →
          ev 15860 (26 + k) = false →
          False)
    (hSize63Diff :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        C.size = 63 →
        PEqualNP.TopForm.IsAO2 26 C →
        (∀ g ∈ C.gates, g.inputs.Nodup) →
        (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
            x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
        have ev : ℕ → ℕ → Bool := fun m w => (C.wires (List.ofFn fun i : Fin 26 => m.testBit i.val)).getD w false
        ∀ (k0 k13 : ℕ) (g0 g13 : PEqualNP.CircuitLowerBounds.Gate),
          k0 < k13 →
          C.gates[k0]? = some g0 →
          g0.op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ev 8193 (26 + k0) = true →
          (∀ u ∈ g0.inputs, ev 1 u = false) →
          ev 8191 (26 + k0) = false →
          ev 25018369 (26 + k0) = false →
          C.gates[k13]? = some g13 →
          g13.op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ev 8193 (26 + k13) = true →
          (∀ u ∈ g13.inputs, ev 8192 u = false) →
          ev 67100672 (26 + k13) = false →
          ev 15860 (26 + k13) = false →
          False)
    (hSize64Same :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        C.size = 64 →
        PEqualNP.TopForm.IsAO2 26 C →
        (∀ g ∈ C.gates, g.inputs.Nodup) →
        (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
            x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
        have ev : ℕ → ℕ → Bool := fun m w => (C.wires (List.ofFn fun i : Fin 26 => m.testBit i.val)).getD w false
        ∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
          C.gates[k]? = some g →
          g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ev 8193 (26 + k) = true →
          (∀ u ∈ g.inputs, ev 1 u = false ∧ ev 8192 u = false) →
          ev 8191 (26 + k) = false →
          ev 25018369 (26 + k) = false →
          ev 67100672 (26 + k) = false →
          ev 15860 (26 + k) = false →
          False)
    (hSize64Diff :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        C.size = 64 →
        PEqualNP.TopForm.IsAO2 26 C →
        (∀ g ∈ C.gates, g.inputs.Nodup) →
        (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
            x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
        have ev : ℕ → ℕ → Bool := fun m w => (C.wires (List.ofFn fun i : Fin 26 => m.testBit i.val)).getD w false
        ∀ (k0 k13 : ℕ) (g0 g13 : PEqualNP.CircuitLowerBounds.Gate),
          k0 < k13 →
          C.gates[k0]? = some g0 →
          g0.op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ev 8193 (26 + k0) = true →
          (∀ u ∈ g0.inputs, ev 1 u = false) →
          ev 8191 (26 + k0) = false →
          ev 25018369 (26 + k0) = false →
          C.gates[k13]? = some g13 →
          g13.op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ev 8193 (26 + k13) = true →
          (∀ u ∈ g13.inputs, ev 8192 u = false) →
          ev 67100672 (26 + k13) = false →
          ev 15860 (26 + k13) = false →
          False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (63 : ℕ) ≤ x1.size →     x1.size ≤ (64 : ℕ) →       PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →         (∀ x5 ∈ x1.gates, x5.inputs.Nodup) →           (∀ (x6 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) →             have x7 : ℕ → ℕ → Bool := fun (x7 x8 : ℕ) => (x1.wires (List.ofFn fun (x9 : Fin (26 : ℕ)) => x7.testBit ↑x9)).getD x8 Bool.false;             ∃ x8 ∈ [(0 : ℕ), (13 : ℕ)],               have x9 : ℕ := if x8 = (0 : ℕ) then (25034751 : ℕ) else (67108341 : ℕ);               have x10 : ℕ := if x8 = (0 : ℕ) then (8191 : ℕ) else (67100672 : ℕ);               have x11 : ℕ := if x8 = (0 : ℕ) then (25018369 : ℕ) else (15860 : ℕ);               ∀ (x12 : Set ℕ), x1.output ∈ x12 → (∀ (x14 : Fin (26 : ℕ)), ↑x14 ∈ x12 → x9.testBit ↑x14 = Bool.false) → ¬∀ (x15 : ℕ) (x16 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x15]? = Option.some x16 → (26 : ℕ) + x15 ∈ x12 → (x16.op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ x20 ∈ x16.inputs, x20 ∈ x12) ∧ (x16.op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ x20 ∈ x16.inputs, x20 ∈ x12) ∨ (∀ x20 ∈ x16.inputs, x7 ((2 : ℕ) ^ x8) x20 = Bool.false) ∧ x7 x10 ((26 : ℕ) + x15) = Bool.false ∧ x7 x11 ((26 : ℕ) + x15) = Bool.false) := by
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
  have getD_snoc_eq (l : List Bool) (a : Bool) : (l ++ [a]).getD l.length false = a := by
    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]
  have getD_snoc_ne (l : List Bool) (a : Bool) (j : ℕ) (hj : j ≠ l.length) :
      (l ++ [a]).getD j false = l.getD j false := by
    by_cases hlt : j < l.length
    · exact List.getD_append _ _ _ _ hlt
    · rw [List.getD_eq_default (l ++ [a]) false (n := j) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
          List.getD_eq_default l false (n := j) (by omega)]
  have run_getD_lt (gs : List Gate) (ws : List Bool) (i : ℕ) (hi : i < ws.length) :
      (run gs ws).getD i false = ws.getD i false := by
    induction gs generalizing ws with
    | nil => rfl
    | cons g rest ih =>
      simp only [run, List.foldl_cons] at ih ⊢
      have hi' : i < (step ws g).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
      rw [ih (step ws g) hi']
      exact List.getD_append _ _ _ _ hi
  have run_getD_gate (gs : List Gate) (ws : List Bool) (j : ℕ) (g : Gate)
      (hj : gs[j]? = some g) (hback : ∀ i ∈ g.inputs, i < ws.length + j) :
      (run gs ws).getD (ws.length + j) false =
        g.op.eval (g.inputs.map fun i => (run gs ws).getD i false) := by
    induction gs generalizing ws j with
    | nil => cases hj
    | cons g0 rest ih =>
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        simp only [Nat.add_zero] at hback ⊢
        change (run rest (step ws g0)).getD ws.length false =
          g0.op.eval (g0.inputs.map fun i => (run rest (step ws g0)).getD i false)
        have hlt : ws.length < (step ws g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
        rw [run_getD_lt rest (step ws g0) ws.length hlt]
        have hstep : (step ws g0).getD ws.length false =
            g0.op.eval (g0.inputs.map fun k => ws.getD k false) := getD_snoc_eq ws _
        rw [hstep]
        congr 1
        apply List.map_congr_left
        intro i hi
        have hlti : i < ws.length := hback i hi
        have hlti' : i < (step ws g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
        rw [run_getD_lt rest (step ws g0) i hlti']
        exact (List.getD_append _ _ _ _ hlti).symm
      | succ j' =>
        simp only [List.getElem?_cons_succ] at hj
        change (run rest (step ws g0)).getD (ws.length + (j' + 1)) false =
          g.op.eval (g.inputs.map fun i => (run rest (step ws g0)).getD i false)
        have hlen : (step ws g0).length = ws.length + 1 := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
        have hidx : ws.length + (j' + 1) = (step ws g0).length + j' := by omega
        rw [hidx]
        exact ih (step ws g0) j' hj (fun i hi => by have := hback i hi; omega)
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
  have hdual_lt_add (k i : ℕ) (hi : i < 26 + k) : dual13 i < 26 + k := by
    by_cases h26 : i < 26
    · have h := hdual_lt26 i h26; omega
    · rw [hdual_ge26 i (by omega)]; exact hi
  let dual13f : Fin 26 → Fin 26 := fun i => ⟨dual13 i.val, hdual_lt26_fin i⟩
  have hdual_cast_val : ∀ p : Fin 13, dual13 (Fin.castAdd 13 p).val = (Fin.natAdd 13 (-p)).val := by decide
  have hdual_nat_val : ∀ l : Fin 13, dual13 (Fin.natAdd 13 l).val = (Fin.castAdd 13 (-l)).val := by decide
  have hdual_cast (p : Fin 13) : dual13f (Fin.castAdd 13 p) = Fin.natAdd 13 (-p) := Fin.ext (hdual_cast_val p)
  have hdual_nat (l : Fin 13) : dual13f (Fin.natAdd 13 l) = Fin.castAdd 13 (-l) := Fin.ext (hdual_nat_val l)
  have hpg_neg : ∀ p l : Fin 13,
      (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ↔
      (-l = -p ∨ -l = -p + 1 ∨ -l = -p + 3 ∨ -l = -p + 9) := by decide
  have h8193_bits : ∀ i : Fin 26, (8193 : ℕ).testBit i.val = true → i.val = 0 ∨ i.val = 13 := by decide
  have hf0_0 : (25034751 : ℕ).testBit 0 = true := by decide
  have hf0_13 : (25034751 : ℕ).testBit 13 = true := by decide
  have hf13_0 : (67108341 : ℕ).testBit 0 = true := by decide
  have hf13_13 : (67108341 : ℕ).testBit 13 = true := by decide
  have hm_8193 : ∀ i : Fin 26, (8193 : ℕ).testBit (dual13 i.val) = (8193 : ℕ).testBit i.val := by decide
  have hm_1_8192 : ∀ i : Fin 26, (1 : ℕ).testBit (dual13 i.val) = (8192 : ℕ).testBit i.val := by decide
  have hm_8192_1 : ∀ i : Fin 26, (8192 : ℕ).testBit (dual13 i.val) = (1 : ℕ).testBit i.val := by decide
  have hm_8191_67100672 : ∀ i : Fin 26, (8191 : ℕ).testBit (dual13 i.val) = (67100672 : ℕ).testBit i.val := by decide
  have hm_67100672_8191 : ∀ i : Fin 26, (67100672 : ℕ).testBit (dual13 i.val) = (8191 : ℕ).testBit i.val := by decide
  have hm_25018369_15860 : ∀ i : Fin 26, (25018369 : ℕ).testBit (dual13 i.val) = (15860 : ℕ).testBit i.val := by decide
  have hm_15860_25018369 : ∀ i : Fin 26, (15860 : ℕ).testBit (dual13 i.val) = (25018369 : ℕ).testBit i.val := by decide
  let dualGate : Gate → Gate := fun g => ⟨g.op, g.inputs.map dual13⟩
  let dualCirc : Circuit → Circuit := fun D => ⟨D.gates.map dualGate, dual13 D.output⟩
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
          rw [hdl, getD_snoc_eq w1 _, hlen, getD_snoc_eq w2 _]
        · have hi2 : i ≠ w2.length := by omega
          have hdi : dual13 i ≠ w1.length := by
            intro heq
            have h1 : i = dual13 w1.length := by rw [← heq, hdual_inv i]
            rw [hdual_ge26 w1.length h26] at h1
            exact hi h1
          rw [getD_snoc_ne w2 _ i hi2, getD_snoc_ne w1 _ (dual13 i) hdi]
          exact hrel i
  intro C hsz63 hsz64 hAO hnd hpg
  dsimp only
  let ev : ℕ → ℕ → Bool := fun m w =>
    (C.wires (List.ofFn fun i : Fin 26 => m.testBit i.val)).getD w false
  obtain ⟨handor, hreads, hlen2⟩ := hAO
  have hev_out_8193 : ev 8193 C.output = true := by
    have h1 := (hpg (fun i : Fin 26 => (8193 : ℕ).testBit i.val)).mpr
      ⟨(0 : Fin 13), (0 : Fin 13), Or.inl rfl, by decide, by decide⟩
    exact h1
  have extract_and (mf ms ma mb : ℕ) (hf0 : mf.testBit 0 = true) (hf13 : mf.testBit 13 = true)
      (S : Set ℕ) (houtS : C.output ∈ S)
      (hinS : ∀ i : Fin 26, i.val ∈ S → mf.testBit i.val = false)
      (hclosed : ∀ j g, C.gates[j]? = some g → 26 + j ∈ S →
        (g.op = GateOp.or → ∀ u ∈ g.inputs, u ∈ S) ∧
        (g.op = GateOp.and → (∃ u ∈ g.inputs, u ∈ S) ∨
          (∀ u ∈ g.inputs, ev ms u = false) ∧ ev ma (26 + j) = false ∧ ev mb (26 + j) = false)) :
      ∃ k g, C.gates[k]? = some g ∧ g.op = GateOp.and ∧ ev 8193 (26 + k) = true ∧
        (∀ u ∈ g.inputs, ev ms u = false) ∧ ev ma (26 + k) = false ∧ ev mb (26 + k) = false := by
    suffices hwalk : ∀ w : ℕ, w ∈ S → ev 8193 w = true →
        ∃ k g, C.gates[k]? = some g ∧ g.op = GateOp.and ∧ ev 8193 (26 + k) = true ∧
          (∀ u ∈ g.inputs, ev ms u = false) ∧ ev ma (26 + k) = false ∧ ev mb (26 + k) = false by
      exact hwalk C.output houtS hev_out_8193
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hwS hwT
      by_cases hw26 : w < 26
      · exfalso
        let wf : Fin 26 := ⟨w, hw26⟩
        have hlt : w < (List.ofFn fun i : Fin 26 => (8193 : ℕ).testBit i.val).length := by
          simp only [List.length_ofFn]; exact hw26
        have hread : ev 8193 w = (8193 : ℕ).testBit w := by
          change (run C.gates (List.ofFn fun i : Fin 26 => (8193 : ℕ).testBit i.val)).getD w false = _
          rw [run_getD_lt C.gates _ w hlt, List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
        rw [hread] at hwT
        have hmf : mf.testBit w = false := hinS wf hwS
        rcases h8193_bits wf hwT with h0 | h13
        · change w = 0 at h0
          rw [h0] at hmf
          rw [hf0] at hmf
          cases hmf
        · change w = 13 at h13
          rw [h13] at hmf
          rw [hf13] at hmf
          cases hmf
      · let k : ℕ := w - 26
        have hwk : 26 + k = w := by omega
        have hk_lt : k < C.gates.length := by
          by_contra hge
          have hlen : (run C.gates (List.ofFn fun i : Fin 26 => (8193 : ℕ).testBit i.val)).length =
              26 + C.gates.length := by
            rw [run_len]; simp only [List.length_ofFn]
          have hfalse : ev 8193 w = false := by
            change (run C.gates (List.ofFn fun i : Fin 26 => (8193 : ℕ).testBit i.val)).getD w false = false
            exact List.getD_eq_default _ false (n := w) (by rw [hlen]; omega)
          rw [hfalse] at hwT
          cases hwT
        let g : Gate := C.gates[k]
        have hk : C.gates[k]? = some g := List.getElem?_eq_getElem hk_lt
        have hg_mem : g ∈ C.gates := List.getElem_mem hk_lt
        have hgat : gateAt C k = g := by
          change C.gates.getD k ⟨GateOp.or, []⟩ = g
          rw [List.getD_eq_getElem _ _ hk_lt]
        have hback : ∀ u ∈ g.inputs, u < 26 + k := by
          intro u hu
          have hb := hreads k hk_lt u
          rw [hgat] at hb
          exact hb hu
        have heval : ev 8193 (26 + k) = g.op.eval (g.inputs.map (ev 8193)) := by
          change (run C.gates (List.ofFn fun i : Fin 26 => (8193 : ℕ).testBit i.val)).getD (26 + k) false =
            g.op.eval (g.inputs.map fun i => (run C.gates (List.ofFn fun j : Fin 26 => (8193 : ℕ).testBit j.val)).getD i false)
          have h := run_getD_gate C.gates (List.ofFn fun i : Fin 26 => (8193 : ℕ).testBit i.val) k g hk
            (by simpa only [List.length_ofFn] using hback)
          simpa only [List.length_ofFn] using h
        have hwTk : ev 8193 (26 + k) = true := by rw [hwk]; exact hwT
        have hwSk : 26 + k ∈ S := by rw [hwk]; exact hwS
        have hcl := hclosed k g hk hwSk
        rcases handor g hg_mem with hop_and | hop_or
        · have hall : ∀ u ∈ g.inputs, ev 8193 u = true := by
            rw [heval, hop_and] at hwTk
            change (g.inputs.map (ev 8193)).all id = true at hwTk
            rw [List.all_eq_true] at hwTk
            intro u hu
            exact hwTk (ev 8193 u) (List.mem_map_of_mem hu)
          rcases hcl.2 hop_and with ⟨u, hu, huS⟩ | ⟨hms, hma, hmb⟩
          · exact ih u (by have := hback u hu; omega) huS (hall u hu)
          · exact ⟨k, g, hk, hop_and, hwTk, hms, hma, hmb⟩
        · rw [heval, hop_or] at hwTk
          change (g.inputs.map (ev 8193)).any id = true at hwTk
          rw [List.any_eq_true] at hwTk
          obtain ⟨b, hb, hbt⟩ := hwTk
          rw [List.mem_map] at hb
          obtain ⟨u, hu, rfl⟩ := hb
          exact ih u (by have := hback u hu; omega) (hcl.1 hop_or u hu) hbt
  by_contra hnot
  have hS0 : ∃ S0 : Set ℕ, C.output ∈ S0 ∧
      (∀ i : Fin 26, i.val ∈ S0 → (25034751 : ℕ).testBit i.val = false) ∧
      ∀ j g, C.gates[j]? = some g → 26 + j ∈ S0 →
        (g.op = GateOp.or → ∀ u ∈ g.inputs, u ∈ S0) ∧
        (g.op = GateOp.and → (∃ u ∈ g.inputs, u ∈ S0) ∨
          (∀ u ∈ g.inputs, ev 1 u = false) ∧ ev 8191 (26 + j) = false ∧ ev 25018369 (26 + j) = false) := by
    by_contra hno
    apply hnot
    refine ⟨0, List.mem_cons_self, ?_⟩
    intro S h1 h2 h3
    exact hno ⟨S, h1, h2, h3⟩
  have hS13 : ∃ S13 : Set ℕ, C.output ∈ S13 ∧
      (∀ i : Fin 26, i.val ∈ S13 → (67108341 : ℕ).testBit i.val = false) ∧
      ∀ j g, C.gates[j]? = some g → 26 + j ∈ S13 →
        (g.op = GateOp.or → ∀ u ∈ g.inputs, u ∈ S13) ∧
        (g.op = GateOp.and → (∃ u ∈ g.inputs, u ∈ S13) ∨
          (∀ u ∈ g.inputs, ev 8192 u = false) ∧ ev 67100672 (26 + j) = false ∧ ev 15860 (26 + j) = false) := by
    by_contra hno
    apply hnot
    refine ⟨13, List.mem_cons_of_mem 0 List.mem_cons_self, ?_⟩
    intro S h1 h2 h3
    exact hno ⟨S, h1, h2, h3⟩
  obtain ⟨S0, houtS0, hinS0, hclS0⟩ := hS0
  obtain ⟨S13, houtS13, hinS13, hclS13⟩ := hS13
  obtain ⟨k0, g0, hk0, hop0, h8193_0, h1_0, h8191_0, h250_0⟩ :=
    extract_and 25034751 1 8191 25018369 hf0_0 hf0_13 S0 houtS0 hinS0 hclS0
  obtain ⟨k13, g13, hk13, hop13, h8193_13, h8192_13, h671_13, h158_13⟩ :=
    extract_and 67108341 8192 67100672 15860 hf13_0 hf13_13 S13 houtS13 hinS13 hclS13
  have hAO_C : IsAO2 26 C := ⟨handor, hreads, hlen2⟩
  have hsz_cases : C.size = 63 ∨ C.size = 64 := by omega
  by_cases heq_k : k0 = k13
  · subst heq_k
    have hgeq : g0 = g13 := by
      rw [hk0] at hk13
      exact Option.some.inj hk13
    subst hgeq
    rcases hsz_cases with h63 | h64
    · exact hSize63Same C h63 hAO_C hnd hpg k0 g0 hk0 hop0 h8193_0
        (fun u hu => ⟨h1_0 u hu, h8192_13 u hu⟩) h8191_0 h250_0 h671_13 h158_13
    · exact hSize64Same C h64 hAO_C hnd hpg k0 g0 hk0 hop0 h8193_0
        (fun u hu => ⟨h1_0 u hu, h8192_13 u hu⟩) h8191_0 h250_0 h671_13 h158_13
  · by_cases hlt_k : k0 < k13
    · rcases hsz_cases with h63 | h64
      · exact hSize63Diff C h63 hAO_C hnd hpg k0 k13 g0 g13 hlt_k
          hk0 hop0 h8193_0 h1_0 h8191_0 h250_0
          hk13 hop13 h8193_13 h8192_13 h671_13 h158_13
      · exact hSize64Diff C h64 hAO_C hnd hpg k0 k13 g0 g13 hlt_k
          hk0 hop0 h8193_0 h1_0 h8191_0 h250_0
          hk13 hop13 h8193_13 h8192_13 h671_13 h158_13
    · have hlt_rev : k13 < k0 := by omega
      let C' : Circuit := dualCirc C
      have hC'_sz : C'.size = C.size := by
        change (C.gates.map dualGate).length = C.gates.length
        exact List.length_map _
      have hC'_AO : IsAO2 26 C' := by
        refine ⟨?_, ?_, ?_⟩
        · intro g' hg'
          change g' ∈ C.gates.map dualGate at hg'
          rw [List.mem_map] at hg'
          obtain ⟨g, hg, rfl⟩ := hg'
          exact handor g hg
        · intro j hj u hu
          have hj' : j < C.gates.length := by
            change j < (C.gates.map dualGate).length at hj
            rw [List.length_map] at hj
            exact hj
          have hgat' : gateAt C' j = dualGate (gateAt C j) := by
            change (C.gates.map dualGate).getD j ⟨GateOp.or, []⟩ =
              dualGate (C.gates.getD j ⟨GateOp.or, []⟩)
            rw [List.getD_eq_getElem _ _ hj, List.getElem_map, List.getD_eq_getElem _ _ hj']
          rw [hgat'] at hu
          change u ∈ (gateAt C j).inputs.map dual13 at hu
          rw [List.mem_map] at hu
          obtain ⟨i, hi, rfl⟩ := hu
          exact hdual_lt_add j i (hreads j hj' i hi)
        · intro g' hg'
          change g' ∈ C.gates.map dualGate at hg'
          rw [List.mem_map] at hg'
          obtain ⟨g, hg, rfl⟩ := hg'
          change (g.inputs.map dual13).length = 2
          rw [List.length_map]
          exact hlen2 g hg
      have hC'_nd : ∀ g' ∈ C'.gates, g'.inputs.Nodup := by
        intro g' hg'
        change g' ∈ C.gates.map dualGate at hg'
        rw [List.mem_map] at hg'
        obtain ⟨g, hg, rfl⟩ := hg'
        exact (hnd g hg).map hdual_inj
      have hC'_wires (f : Fin 26 → Bool) (i : ℕ) :
          (C'.wires (List.ofFn f)).getD i false =
            (C.wires (List.ofFn fun j : Fin 26 => f (dual13f j))).getD (dual13 i) false := by
        have hrel : ∀ j : ℕ, (List.ofFn f).getD j false =
            (List.ofFn fun t : Fin 26 => f (dual13f t)).getD (dual13 j) false := by
          intro j
          by_cases hj : j < 26
          · have hdj : dual13 j < 26 := hdual_lt26 j hj
            have h1 : j < (List.ofFn f).length := by simp only [List.length_ofFn]; exact hj
            have h2 : dual13 j < (List.ofFn fun t : Fin 26 => f (dual13f t)).length := by
              simp only [List.length_ofFn]; exact hdj
            rw [List.getD_eq_getElem _ _ h1, List.getElem_ofFn,
                List.getD_eq_getElem _ _ h2, List.getElem_ofFn]
            congr 1
            apply Fin.ext
            change j = dual13 (dual13 j)
            exact (hdual_inv j).symm
          · rw [hdual_ge26 j (by omega),
                List.getD_eq_default _ false (n := j) (by simp only [List.length_ofFn]; omega),
                List.getD_eq_default _ false (n := j) (by simp only [List.length_ofFn]; omega)]
        exact run_dual C.gates (List.ofFn fun t : Fin 26 => f (dual13f t)) (List.ofFn f)
          (by simp only [List.length_ofFn]) (by simp only [List.length_ofFn]; omega) hrel i
      have hC'_pg : ∀ x : Fin 26 → Bool, C'.eval (List.ofFn x) = true ↔
          ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
            x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
        intro x
        have hev' : C'.eval (List.ofFn x) = C.eval (List.ofFn fun j : Fin 26 => x (dual13f j)) := by
          change (C'.wires (List.ofFn x)).getD (dual13 C.output) false =
            (C.wires (List.ofFn fun j : Fin 26 => x (dual13f j))).getD C.output false
          rw [hC'_wires x (dual13 C.output), hdual_inv C.output]
        rw [hev', hpg]
        constructor
        · rintro ⟨p, l, hinc, hp, hl⟩
          rw [hdual_cast p] at hp
          rw [hdual_nat l] at hl
          exact ⟨-l, -p, (hpg_neg p l).mp hinc, hl, hp⟩
        · rintro ⟨p, l, hinc, hp, hl⟩
          refine ⟨-l, -p, ?_, ?_, ?_⟩
          · have h := (hpg_neg (-l) (-p)).mpr
            rw [neg_neg, neg_neg] at h
            exact h hinc
          · rw [hdual_cast (-l), neg_neg]; exact hl
          · rw [hdual_nat (-p), neg_neg]; exact hp
      let ev' : ℕ → ℕ → Bool := fun m w =>
        (C'.wires (List.ofFn fun i : Fin 26 => m.testBit i.val)).getD w false
      have hev'_mask (m1 m2 : ℕ) (hm : ∀ i : Fin 26, m1.testBit (dual13 i.val) = m2.testBit i.val)
          (w : ℕ) : ev' m1 w = ev m2 (dual13 w) := by
        dsimp only [ev', ev]
        rw [hC'_wires (fun i : Fin 26 => m1.testBit i.val) w]
        have hfn : (fun j : Fin 26 => m1.testBit (dual13f j).val) =
            (fun j : Fin 26 => m2.testBit j.val) := funext hm
        rw [hfn]
      have hk0' : C'.gates[k13]? = some (dualGate g13) := by
        change (C.gates.map dualGate)[k13]? = some (dualGate g13)
        rw [List.getElem?_map, hk13]; rfl
      have hk13' : C'.gates[k0]? = some (dualGate g0) := by
        change (C.gates.map dualGate)[k0]? = some (dualGate g0)
        rw [List.getElem?_map, hk0]; rfl
      have h8193_0' : ev' 8193 (26 + k13) = true := by
        rw [hev'_mask 8193 8193 hm_8193 (26 + k13), hdual_ge26 (26 + k13) (by omega)]
        exact h8193_13
      have h1_0' : ∀ u ∈ (dualGate g13).inputs, ev' 1 u = false := by
        intro u hu
        change u ∈ g13.inputs.map dual13 at hu
        rw [List.mem_map] at hu
        obtain ⟨v, hv, rfl⟩ := hu
        rw [hev'_mask 1 8192 hm_1_8192 (dual13 v), hdual_inv v]
        exact h8192_13 v hv
      have h8191_0' : ev' 8191 (26 + k13) = false := by
        rw [hev'_mask 8191 67100672 hm_8191_67100672 (26 + k13), hdual_ge26 (26 + k13) (by omega)]
        exact h671_13
      have h250_0' : ev' 25018369 (26 + k13) = false := by
        rw [hev'_mask 25018369 15860 hm_25018369_15860 (26 + k13), hdual_ge26 (26 + k13) (by omega)]
        exact h158_13
      have h8193_13' : ev' 8193 (26 + k0) = true := by
        rw [hev'_mask 8193 8193 hm_8193 (26 + k0), hdual_ge26 (26 + k0) (by omega)]
        exact h8193_0
      have h8192_13' : ∀ u ∈ (dualGate g0).inputs, ev' 8192 u = false := by
        intro u hu
        change u ∈ g0.inputs.map dual13 at hu
        rw [List.mem_map] at hu
        obtain ⟨v, hv, rfl⟩ := hu
        rw [hev'_mask 8192 1 hm_8192_1 (dual13 v), hdual_inv v]
        exact h1_0 v hv
      have h671_13' : ev' 67100672 (26 + k0) = false := by
        rw [hev'_mask 67100672 8191 hm_67100672_8191 (26 + k0), hdual_ge26 (26 + k0) (by omega)]
        exact h8191_0
      have h158_13' : ev' 15860 (26 + k0) = false := by
        rw [hev'_mask 15860 25018369 hm_15860_25018369 (26 + k0), hdual_ge26 (26 + k0) (by omega)]
        exact h250_0
      rcases hsz_cases with h63 | h64
      · exact hSize63Diff C' (hC'_sz.trans h63) hC'_AO hC'_nd hC'_pg k13 k0 (dualGate g13) (dualGate g0) hlt_rev
          hk0' hop13 h8193_0' h1_0' h8191_0' h250_0'
          hk13' hop0 h8193_13' h8192_13' h671_13' h158_13'
      · exact hSize64Diff C' (hC'_sz.trans h64) hC'_AO hC'_nd hC'_pg k13 k0 (dualGate g13) (dualGate g0) hlt_rev
          hk0' hop13 h8193_0' h1_0' h8191_0' h250_0'
          hk13' hop0 h8193_13' h8192_13' h671_13' h158_13'
