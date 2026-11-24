import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CircuitMoves

theorem PEqualNP.Outside.R_meta_2640_17
    (hMono :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n))
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        (¬ G.Colorable 2 ∧
          (∀ v ∉ S, (G.neighborSet v).ncard = 3) ∧
          (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) ∧
          (∀ u v : Fin n, G.Adj u v → u ∉ S)) →
        (PEqualNP.MetaComplexity.IsMinimalCircuit n C ∧
          PEqualNP.MetaComplexity.Monotone2 C ∧
          PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G S ∧
          (∀ u v : Fin n, G.Adj u v → (C.gates.countP fun g => decide (u.val ∈ g.inputs ∨ v.val ∈ g.inputs)) ≤ 6)) →
        ∃ (u v : Fin n),
          G.Adj u v ∧
          ∃ (seq : ℕ → PEqualNP.CircuitLowerBounds.Circuit),
            PEqualNP.MetaComplexity.FanInTwo (seq 0) ∧
            (seq 0).size ≤ C.size ∧
            PEqualNP.MetaComplexity.circuitFun n (seq 0) = PEqualNP.MetaComplexity.circuitFun n C ∧
            ∀ k < 7,
              ∃ (idx repl : ℕ),
                idx < (seq k).size ∧
                (repl < n + idx ∨ n + (seq k).size ≤ repl) ∧
                seq (k + 1) = PEqualNP.CircuitMoves.eraseGate n (seq k) idx repl ∧
                ((∀ x : Fin n → Bool,
                    have w : List Bool := (seq k).wires (List.ofFn (Function.update (Function.update x u false) v false))
                    w.getD (n + idx) false = w.getD repl false) ∨
                  ((seq k).output ≠ n + idx ∧ ∀ g ∈ List.drop (idx + 1) (seq k).gates, n + idx ∉ g.inputs)))
    (hNotInput :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n))
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        (¬ G.Colorable 2 ∧
          (∀ v ∉ S, (G.neighborSet v).ncard = 3) ∧
          (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) ∧
          (∀ u v : Fin n, G.Adj u v → u ∉ S)) →
        (PEqualNP.MetaComplexity.IsMinimalCircuit n C ∧
          (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∃ w ∈ g.inputs, w < n) ∧
          PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G S ∧
          (∀ u v : Fin n, G.Adj u v →
            (C.gates.countP fun g => !g.op.eval [false] && decide (u.val ∈ g.inputs ∨ v.val ∈ g.inputs)) ≤ 6)) →
        ∃ (u v : Fin n),
          G.Adj u v ∧
          ∃ (seq : ℕ → PEqualNP.CircuitLowerBounds.Circuit),
            PEqualNP.MetaComplexity.FanInTwo (seq 0) ∧
            (seq 0).size ≤ C.size ∧
            PEqualNP.MetaComplexity.circuitFun n (seq 0) = PEqualNP.MetaComplexity.circuitFun n C ∧
            ∀ k < 7,
              ∃ (idx repl : ℕ),
                idx < (seq k).size ∧
                (repl < n + idx ∨ n + (seq k).size ≤ repl) ∧
                seq (k + 1) = PEqualNP.CircuitMoves.eraseGate n (seq k) idx repl ∧
                ((∀ x : Fin n → Bool,
                    have w : List Bool := (seq k).wires (List.ofFn (Function.update (Function.update x u false) v false))
                    w.getD (n + idx) false = w.getD repl false) ∨
                  ((seq k).output ≠ n + idx ∧ ∀ g ∈ List.drop (idx + 1) (seq k).gates, n + idx ∉ g.inputs)))
    (hNotInternal :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n))
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        (¬ G.Colorable 2 ∧
          (∀ v ∉ S, (G.neighborSet v).ncard = 3) ∧
          (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) ∧
          (∀ u v : Fin n, G.Adj u v → u ∉ S)) →
        (PEqualNP.MetaComplexity.IsMinimalCircuit n C ∧
          (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
          (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not → ∀ w ∈ g.inputs, n ≤ w) ∧
          PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G S ∧
          (∀ u v : Fin n, G.Adj u v →
            (C.gates.countP fun g => !g.op.eval [false] && decide (u.val ∈ g.inputs ∨ v.val ∈ g.inputs)) ≤ 6)) →
        ∃ (u v : Fin n),
          G.Adj u v ∧
          ∃ (seq : ℕ → PEqualNP.CircuitLowerBounds.Circuit),
            PEqualNP.MetaComplexity.FanInTwo (seq 0) ∧
            (seq 0).size ≤ C.size ∧
            PEqualNP.MetaComplexity.circuitFun n (seq 0) = PEqualNP.MetaComplexity.circuitFun n C ∧
            ∀ k < 7,
              ∃ (idx repl : ℕ),
                idx < (seq k).size ∧
                (repl < n + idx ∨ n + (seq k).size ≤ repl) ∧
                seq (k + 1) = PEqualNP.CircuitMoves.eraseGate n (seq k) idx repl ∧
                ((∀ x : Fin n → Bool,
                    have w : List Bool := (seq k).wires (List.ofFn (Function.update (Function.update x u false) v false))
                    w.getD (n + idx) false = w.getD repl false) ∨
                  ((seq k).output ≠ n + idx ∧ ∀ g ∈ List.drop (idx + 1) (seq k).gates, n + idx ∉ g.inputs))) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   ¬x2.Colorable (2 : ℕ) →     (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →       (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →         (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →           (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →             PEqualNP.MetaComplexity.IsMinimalCircuit x1 x4 →               (∀ (x11 : Fin x1 → Bool), x4.eval (List.ofFn x11) = Bool.true ↔ (∃ x12 ∈ x3, x11 x12 = Bool.true) ∨ ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) →                 ∃ (x12 : Fin x1) (x13 : Fin x1),                   x2.Adj x12 x13 ∧                     ∃ (x14 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),                       PEqualNP.MetaComplexity.FanInTwo (x14 (0 : ℕ)) ∧                         (x14 (0 : ℕ)).size ≤ x4.size ∧                           PEqualNP.MetaComplexity.circuitFun x1 (x14 (0 : ℕ)) = PEqualNP.MetaComplexity.circuitFun x1 x4 ∧                             ∀ x15 < (7 : ℕ),                               ∃ (x17 : ℕ) (x18 : ℕ),                                 x17 < (x14 x15).size ∧                                   (x18 < x1 + x17 ∨ x1 + (x14 x15).size ≤ x18) ∧                                     x14 (x15 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (x14 x15) x17 x18 ∧                                       ((∀ (x19 : Fin x1 → Bool),                                           have x20 : List Bool := (x14 x15).wires (List.ofFn (Function.update (Function.update x19 x12 Bool.false) x13 Bool.false));                                           x20.getD (x1 + x17) Bool.false = x20.getD x18 Bool.false) ∨                                         (x14 x15).output ≠ x1 + x17 ∧ ∀ x19 ∈ List.drop (x17 + (1 : ℕ)) (x14 x15).gates, x1 + x17 ∉ x19.inputs) := by
  intro n G S C hnc hdeg hgirth hS _ hmin hfun_iff
  let _ : DecidableRel G.Adj := Classical.decRel G.Adj
  have hfun : PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G S := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change C.eval (List.ofFn x) = true ↔
      (decide (∃ a ∈ S, x a = true) || decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) = true
    rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    exact hfun_iff x
  by_cases hhigh : ∃ u v : Fin n, G.Adj u v ∧
      7 ≤ C.gates.countP (fun g => !g.op.eval [false] && decide (u.val ∈ g.inputs ∨ v.val ∈ g.inputs))
  · obtain ⟨u, v, huv, hcnt⟩ := hhigh
    let P : Gate → Bool := fun g => !g.op.eval [false] && decide (u.val ∈ g.inputs ∨ v.val ∈ g.inputs)
    have hextract_inc : ∀ (l : List Gate) (m : ℕ), m ≤ l.countP P →
        ∃ I : List ℕ, I.length = m ∧ I.Pairwise (· < ·) ∧
          ∀ j ∈ I, ∃ hj : j < l.length, P (l[j]'hj) = true := by
      intro l
      induction l with
      | nil =>
        intro m hm
        simp only [List.countP_nil, Nat.le_zero] at hm
        subst hm
        exact ⟨[], rfl, List.Pairwise.nil, fun _ h => by cases h⟩
      | cons g rest ih =>
        intro m hm
        rw [List.countP_cons] at hm
        cases hPg : P g with
        | false =>
          rw [hPg] at hm
          simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hm
          obtain ⟨I, hIlen, hIpw, hImem⟩ := ih m hm
          refine ⟨I.map (· + 1), by rw [List.length_map, hIlen], ?_, ?_⟩
          · rw [List.pairwise_map]
            exact hIpw.imp (fun h => Nat.add_lt_add_right h 1)
          · intro j hj
            rw [List.mem_map] at hj
            obtain ⟨j0, hj0, rfl⟩ := hj
            obtain ⟨hlt, hP0⟩ := hImem j0 hj0
            exact ⟨Nat.add_lt_add_right hlt 1, hP0⟩
        | true =>
          rw [hPg] at hm
          simp only [↓reduceIte] at hm
          cases m with
          | zero =>
            exact ⟨[], rfl, List.Pairwise.nil, fun _ h => by cases h⟩
          | succ m' =>
            obtain ⟨I, hIlen, hIpw, hImem⟩ := ih m' (by omega)
            refine ⟨0 :: I.map (· + 1), by simp only [List.length_cons, List.length_map, hIlen], ?_, ?_⟩
            · rw [List.pairwise_cons]
              refine ⟨fun j hj => ?_, ?_⟩
              · rw [List.mem_map] at hj
                obtain ⟨j0, _, rfl⟩ := hj
                omega
              · rw [List.pairwise_map]
                exact hIpw.imp (fun h => Nat.add_lt_add_right h 1)
            · intro j hj
              rcases List.mem_cons.mp hj with rfl | hj'
              · exact ⟨Nat.zero_lt_succ _, hPg⟩
              · rw [List.mem_map] at hj'
                obtain ⟨j0, hj0, rfl⟩ := hj'
                obtain ⟨hlt, hP0⟩ := hImem j0 hj0
                exact ⟨Nat.add_lt_add_right hlt 1, hP0⟩
    obtain ⟨Iinc, hIlen, hIpw, hImem⟩ := hextract_inc C.gates 7 hcnt
    let J : List ℕ := Iinc.reverse
    have hJlen : J.length = 7 := by dsimp only [J]; rw [List.length_reverse, hIlen]
    have hJpw : J.Pairwise (· > ·) := by
      dsimp only [J]
      rw [List.pairwise_reverse]
      exact hIpw
    let idx : ℕ → ℕ := fun k => J.getD k 0
    have hidx_eq (k : ℕ) (hk : k < 7) : idx k = J[k]'(by rw [hJlen]; exact hk) :=
      List.getD_eq_getElem J 0 (by rw [hJlen]; exact hk)
    have hidx_mem (k : ℕ) (hk : k < 7) : idx k ∈ Iinc := by
      rw [hidx_eq k hk]
      exact List.mem_reverse.mp (List.getElem_mem (by rw [hJlen]; exact hk))
    have hidx_lt (k : ℕ) (hk : k < 7) : idx k < C.gates.length := (hImem (idx k) (hidx_mem k hk)).1
    have hidx_P (k : ℕ) (hk : k < 7) : P (C.gates[idx k]'(hidx_lt k hk)) = true := (hImem (idx k) (hidx_mem k hk)).2
    have hidx_strict (k : ℕ) (hk : k + 1 < 7) : idx (k + 1) < idx k := by
      rw [hidx_eq k (by omega), hidx_eq (k + 1) hk]
      exact List.pairwise_iff_getElem.mp hJpw k (k + 1) (by omega) (by omega) (Nat.lt_succ_self k)
    have hidx_bound : ∀ k < 7, idx k + k < C.gates.length := by
      intro k
      induction k with
      | zero => intro hk; simpa only [Nat.add_zero] using hidx_lt 0 hk
      | succ k' ih =>
        intro hk
        have h1 := ih (by omega)
        have h2 := hidx_strict k' hk
        omega
    let replOf : ℕ → ℕ → Gate → ℕ := fun k idxk g =>
      GateOp.rec
        (n + (C.gates.length - k))
        (List.casesOn g.inputs (n + (C.gates.length - k)) (fun a rest =>
          List.casesOn rest (n + (C.gates.length - k)) (fun b _ =>
            if a = u.val ∨ a = v.val then
              if b < n + idxk then b else n + (C.gates.length - k)
            else
              if a < n + idxk then a else n + (C.gates.length - k))))
        (n + (C.gates.length - k))
        (fun _ => n + (C.gates.length - k))
        (n + (C.gates.length - k))
        g.op
    let repl : ℕ → ℕ := fun k => replOf k (idx k) (C.gates.getD (idx k) ⟨GateOp.or, []⟩)
    let seq : ℕ → Circuit := fun k =>
      Nat.rec C (fun m prev => eraseGate n prev (idx m) (repl m)) k
    have hseq_inv : ∀ k ≤ 7, (seq k).gates.length = C.gates.length - k ∧
        ∀ m, (k = 0 ∨ m ≤ idx (k - 1)) → (seq k).gates.take m = C.gates.take m := by
      intro k
      induction k with
      | zero => intro _; exact ⟨by simp only [Nat.sub_zero]; rfl, fun _ _ => rfl⟩
      | succ k' ih =>
        intro hk1
        obtain ⟨hlen_k, htake_k⟩ := ih (by omega)
        have hidx_lt_k : idx k' < (seq k').gates.length := by
          have hb := hidx_bound k' (by omega); omega
        have hgates_succ : (seq (k' + 1)).gates = (seq k').gates.take (idx k') ++
            ((seq k').gates.drop (idx k' + 1)).map (fun g => ⟨g.op, g.inputs.map (eraseRedirect n (idx k') (repl k'))⟩) := by
          change (if idx k' < (seq k').gates.length then
            { gates := (seq k').gates.take (idx k') ++
                ((seq k').gates.drop (idx k' + 1)).map (fun g => ⟨g.op, g.inputs.map (eraseRedirect n (idx k') (repl k'))⟩),
              output := eraseRedirect n (idx k') (repl k') (seq k').output }
            else seq k').gates = _
          simp only [hidx_lt_k, ↓reduceIte]
        refine ⟨?_, ?_⟩
        · rw [hgates_succ, List.length_append, List.length_take, List.length_map, List.length_drop]
          omega
        · intro m hm
          rcases hm with h0 | hm_le
          · omega
          · simp only [Nat.add_sub_cancel] at hm_le
            rw [hgates_succ, List.take_append_of_le_length (by rw [List.length_take]; omega),
                List.take_take, Nat.min_eq_left hm_le]
            apply htake_k m
            cases k' with
            | zero => exact Or.inl rfl
            | succ k'' =>
              exact Or.inr (Nat.le_trans hm_le (Nat.le_of_lt (hidx_strict k'' (by omega))))
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
    have all_id_false (l : List Bool) (hf : false ∈ l) : l.all id = false := by
      induction l with
      | nil => cases hf
      | cons b rest ih =>
        rw [List.all_cons]
        rcases List.mem_cons.mp hf with rfl | hrest
        · rfl
        · rw [ih hrest, Bool.and_false]
    refine ⟨u, v, huv, seq, hmin.1, Nat.le_refl _, rfl, ?_⟩
    intro k hk
    obtain ⟨hlen_k, htake_k⟩ := hseq_inv k (by omega)
    have hidx_lt_k : idx k < (seq k).gates.length := by
      have hb := hidx_bound k hk; omega
    have htake_succ : (seq k).gates.take (idx k + 1) = C.gates.take (idx k + 1) := by
      apply htake_k (idx k + 1)
      cases k with
      | zero => exact Or.inl rfl
      | succ k' => exact Or.inr (hidx_strict k' hk)
    let g : Gate := C.gates[idx k]'(hidx_lt k hk)
    have hg_eq : (seq k).gates[idx k]'hidx_lt_k = g := by
      have h1 := congrArg (fun l => l.getD (idx k) ⟨GateOp.or, []⟩) htake_succ
      have hl1 : idx k < ((seq k).gates.take (idx k + 1)).length := by rw [List.length_take]; omega
      have hl2 : idx k < (C.gates.take (idx k + 1)).length := by rw [List.length_take]; omega
      rw [List.getD_eq_getElem _ _ hl1, List.getD_eq_getElem _ _ hl2,
          List.getElem_take, List.getElem_take] at h1
      exact h1
    have hrepl_eq : repl k = replOf k (idx k) g := by
      dsimp only [repl, g]
      rw [List.getD_eq_getElem C.gates ⟨GateOp.or, []⟩ (hidx_lt k hk)]
    have hg_fan := hmin.1 g (List.getElem_mem (hidx_lt k hk))
    have hg_P : P g = true := hidx_P k hk
    have hg_eval_f : g.op.eval [false] = false := by
      dsimp only [P] at hg_P
      rw [Bool.and_eq_true, Bool.not_eq_true'] at hg_P
      exact hg_P.1
    have hg_uv : u.val ∈ g.inputs ∨ v.val ∈ g.inputs := by
      dsimp only [P] at hg_P
      rw [Bool.and_eq_true, decide_eq_true_eq] at hg_P
      exact hg_P.2
    have hg_op : g.op = GateOp.and ∨ g.op = GateOp.or := by
      rcases hg_fan.1 with h1 | h2 | h3
      · exact Or.inl h1
      · exact Or.inr h2
      · rw [h3] at hg_eval_f
        change true = false at hg_eval_f
        exact Bool.noConfusion hg_eval_f
    refine ⟨idx k, repl k, hidx_lt_k, ?_, rfl, Or.inl ?_⟩
    · rw [hrepl_eq]
      change replOf k (idx k) g < n + idx k ∨ n + (seq k).gates.length ≤ replOf k (idx k) g
      rw [hlen_k]
      dsimp only [replOf]
      rcases hg_op with hop | hop
      · rw [hop]; exact Or.inr (Nat.le_refl _)
      · rw [hop]
        dsimp only
        cases g.inputs with
        | nil => exact Or.inr (Nat.le_refl _)
        | cons a rest =>
          cases rest with
          | nil => exact Or.inr (Nat.le_refl _)
          | cons b _ =>
            dsimp only
            split_ifs with h1 h2 h3
            · exact Or.inl h2
            · exact Or.inr (Nat.le_refl _)
            · exact Or.inl h3
            · exact Or.inr (Nat.le_refl _)
    · intro x
      dsimp only
      let x' : Fin n → Bool := Function.update (Function.update x u false) v false
      have hx'u : x' u = false := by
        dsimp only [x']
        by_cases huv_eq : u = v
        · subst huv_eq; simp only [Function.update_self]
        · simp only [Function.update_of_ne huv_eq, Function.update_self]
      have hx'v : x' v = false := by simp only [x', Function.update_self]
      let w0 : List Bool := List.ofFn x'
      have hw0_len : w0.length = n := List.length_ofFn
      let w_pre : List Bool := run ((seq k).gates.take (idx k)) w0
      have hwpre_len : w_pre.length = n + idx k := by
        dsimp only [w_pre]
        rw [run_len, hw0_len, List.length_take]
        omega
      have hsplit : (seq k).gates = (seq k).gates.take (idx k) ++ (g :: (seq k).gates.drop (idx k + 1)) := by
        rw [← hg_eq, ← List.drop_eq_getElem_cons hidx_lt_k, List.take_append_drop]
      have hw_eq : (seq k).wires w0 = run ((seq k).gates.drop (idx k + 1)) (step w_pre g) := by
        change run (seq k).gates w0 = _
        have h1 : run (seq k).gates w0 = run ((seq k).gates.take (idx k) ++ (g :: (seq k).gates.drop (idx k + 1))) w0 :=
          congrArg (fun gs => run gs w0) hsplit
        rw [h1]
        dsimp only [run, w_pre]
        rw [List.foldl_append, List.foldl_cons]
      have hw_len : ((seq k).wires w0).length = n + (seq k).gates.length := by
        change (run (seq k).gates w0).length = _
        rw [run_len, hw0_len]
      have hw_at_idx : ((seq k).wires w0).getD (n + idx k) false =
          g.op.eval (g.inputs.map fun i => w_pre.getD i false) := by
        rw [hw_eq, run_keep _ _ (n + idx k) (by simp only [step, List.length_append, hwpre_len, List.length_cons, List.length_nil]; omega)]
        dsimp only [step]
        simpa only [hwpre_len] using getD_snoc_eq w_pre (g.op.eval (g.inputs.map fun i => w_pre.getD i false)) false
      have hw_lt_idx (r : ℕ) (hr : r < n + idx k) : ((seq k).wires w0).getD r false = w_pre.getD r false := by
        rw [hw_eq, run_keep _ _ r (by simp only [step, List.length_append, hwpre_len, List.length_cons, List.length_nil]; omega)]
        exact List.getD_append w_pre _ false r (by rw [hwpre_len]; exact hr)
      have hw_ge_len (r : ℕ) (hr : n + (C.gates.length - k) ≤ r) : ((seq k).wires w0).getD r false = false :=
        List.getD_eq_default _ false (n := r) (by rw [hw_len, hlen_k]; exact hr)
      have hwpre_u : w_pre.getD u.val false = false := by
        dsimp only [w_pre]
        rw [run_keep _ w0 u.val (by rw [hw0_len]; exact u.isLt)]
        dsimp only [w0]
        rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact u.isLt), List.getElem_ofFn]
        exact hx'u
      have hwpre_v : w_pre.getD v.val false = false := by
        dsimp only [w_pre]
        rw [run_keep _ w0 v.val (by rw [hw0_len]; exact v.isLt)]
        dsimp only [w0]
        rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact v.isLt), List.getElem_ofFn]
        exact hx'v
      change ((seq k).wires w0).getD (n + idx k) false = ((seq k).wires w0).getD (repl k) false
      rw [hw_at_idx, hrepl_eq]
      dsimp only [replOf]
      rcases hg_op with hop | hop
      · rw [hop]
        dsimp only
        rw [hw_ge_len _ (Nat.le_refl _)]
        change (g.inputs.map fun i => w_pre.getD i false).all id = false
        apply all_id_false
        rw [List.mem_map]
        rcases hg_uv with hu | hv
        · exact ⟨u.val, hu, hwpre_u⟩
        · exact ⟨v.val, hv, hwpre_v⟩
      · rw [hop]
        dsimp only
        cases hins : g.inputs with
        | nil =>
          rw [hins] at hg_uv
          rcases hg_uv with h | h <;> cases h
        | cons a rest =>
          cases rest with
          | nil =>
            dsimp only
            rw [hw_ge_len _ (Nat.le_refl _)]
            rw [hins] at hg_uv
            have ha : a = u.val ∨ a = v.val := by
              rcases hg_uv with hu | hv
              · exact Or.inl (List.mem_singleton.mp hu).symm
              · exact Or.inr (List.mem_singleton.mp hv).symm
            change (w_pre.getD a false || false) = false
            rcases ha with rfl | rfl
            · rw [hwpre_u]; rfl
            · rw [hwpre_v]; rfl
          | cons b rest2 =>
            cases rest2 with
            | cons _ _ =>
              have hlen := hg_fan.2
              rw [hins] at hlen
              simp only [List.length_cons] at hlen
              omega
            | nil =>
              dsimp only
              change (w_pre.getD a false || (w_pre.getD b false || false)) = _
              rw [Bool.or_false]
              split_ifs with ha_uv hb_lt ha_lt
              · have hwa : w_pre.getD a false = false := by
                  rcases ha_uv with rfl | rfl
                  · exact hwpre_u
                  · exact hwpre_v
                rw [hwa, Bool.false_or, hw_lt_idx b hb_lt]
              · have hwa : w_pre.getD a false = false := by
                  rcases ha_uv with rfl | rfl
                  · exact hwpre_u
                  · exact hwpre_v
                have hwb : w_pre.getD b false = false :=
                  List.getD_eq_default w_pre false (n := b) (by rw [hwpre_len]; omega)
                rw [hwa, hwb, hw_ge_len _ (Nat.le_refl _)]; rfl
              · have hb_uv : b = u.val ∨ b = v.val := by
                  rw [hins] at hg_uv
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg_uv
                  rcases hg_uv with (rfl | rfl) | (rfl | rfl)
                  · exact False.elim (ha_uv (Or.inl rfl))
                  · exact Or.inl rfl
                  · exact False.elim (ha_uv (Or.inr rfl))
                  · exact Or.inr rfl
                have hwb : w_pre.getD b false = false := by
                  rcases hb_uv with rfl | rfl
                  · exact hwpre_u
                  · exact hwpre_v
                rw [hwb, Bool.or_false, hw_lt_idx a ha_lt]
              · have hb_uv : b = u.val ∨ b = v.val := by
                  rw [hins] at hg_uv
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg_uv
                  rcases hg_uv with (rfl | rfl) | (rfl | rfl)
                  · exact False.elim (ha_uv (Or.inl rfl))
                  · exact Or.inl rfl
                  · exact False.elim (ha_uv (Or.inr rfl))
                  · exact Or.inr rfl
                have hwb : w_pre.getD b false = false := by
                  rcases hb_uv with rfl | rfl
                  · exact hwpre_u
                  · exact hwpre_v
                have hwa : w_pre.getD a false = false :=
                  List.getD_eq_default w_pre false (n := a) (by rw [hwpre_len]; omega)
                rw [hwa, hwb, hw_ge_len _ (Nat.le_refl _)]; rfl
  · have hlow : ∀ u v : Fin n, G.Adj u v →
        C.gates.countP (fun g => !g.op.eval [false] && decide (u.val ∈ g.inputs ∨ v.val ∈ g.inputs)) ≤ 6 := by
      intro u v huv
      by_contra hgt
      exact hhigh ⟨u, v, huv, by omega⟩
    by_cases hnot : ∃ g ∈ C.gates, g.op = GateOp.not
    · by_cases hnot_in : ∃ g ∈ C.gates, g.op = GateOp.not ∧ ∃ w ∈ g.inputs, w < n
      · exact hNotInput n G S C ⟨hnc, hdeg, hgirth, hS⟩ ⟨hmin, hnot_in, hfun, hlow⟩
      · have hnot_int : ∀ g ∈ C.gates, g.op = GateOp.not → ∀ w ∈ g.inputs, n ≤ w := by
          intro g hg hop w hw
          by_contra hlt
          exact hnot_in ⟨g, hg, hop, w, hw, by omega⟩
        exact hNotInternal n G S C ⟨hnc, hdeg, hgirth, hS⟩ ⟨hmin, hnot, hnot_int, hfun, hlow⟩
    · have hmono : Monotone2 C := by
        intro g hg
        have hgf := hmin.1 g hg
        refine ⟨?_, hgf.2⟩
        rcases hgf.1 with h1 | h2 | h3
        · exact Or.inl h1
        · exact Or.inr h2
        · exact False.elim (hnot ⟨g, hg, h3⟩)
      have hcount_congr : ∀ (l : List Gate) (p q : Gate → Bool), (∀ g ∈ l, p g = q g) → l.countP p = l.countP q := by
        intro l p q
        induction l with
        | nil => intro _; rfl
        | cons g rest ih =>
          intro h
          rw [List.countP_cons, List.countP_cons, h g List.mem_cons_self,
              ih (fun g' hg' => h g' (List.mem_cons_of_mem g hg'))]
      have hlow_mono : ∀ u v : Fin n, G.Adj u v →
          C.gates.countP (fun g => decide (u.val ∈ g.inputs ∨ v.val ∈ g.inputs)) ≤ 6 := by
        intro u v huv
        have heq : C.gates.countP (fun g => decide (u.val ∈ g.inputs ∨ v.val ∈ g.inputs)) =
            C.gates.countP (fun g => !g.op.eval [false] && decide (u.val ∈ g.inputs ∨ v.val ∈ g.inputs)) := by
          apply hcount_congr
          intro g hg
          rcases (hmono g hg).1 with h1 | h2
          · rw [h1]; rfl
          · rw [h2]; rfl
        rw [heq]
        exact hlow u v huv
      exact hMono n G S C ⟨hnc, hdeg, hgirth, hS⟩ ⟨hmin, hmono, hfun, hlow_mono⟩
