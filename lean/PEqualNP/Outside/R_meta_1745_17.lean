import Mathlib.Combinatorics.SimpleGraph.Paths
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_1745_17
    (hMonoAllOr : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ v ∉ S, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → 7 ≤ c.length) →
      (∀ u v : Fin n, G.Adj u v → u ∉ S) →
      (∃ u v : Fin n, G.Adj u v) →
      have F : (Fin n → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun G S
      have eff : PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun g =>
        g.inputs.take (bif g.op.eval [false] then 1 else 2)
      have rd : Fin n → List PEqualNP.CircuitLowerBounds.Gate := fun v =>
        C.gates.filter (fun g => (eff g).contains v.val)
      PEqualNP.MetaComplexity.IsMinimalCircuit n C →
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.circuitFun n C = F →
      (∀ v ∉ S, 1 ≤ (rd v).length ∧ (rd v).length ≤ 3 ∧ ∀ g ∈ rd v, g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      ∃ v ∉ S, ∃ s : ℕ, s + 4 ≤ C.size ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun x => F (Function.update x v false)) s)
    (hMonoHasAnd : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ v ∉ S, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → 7 ≤ c.length) →
      (∀ u v : Fin n, G.Adj u v → u ∉ S) →
      (∃ u v : Fin n, G.Adj u v) →
      have F : (Fin n → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun G S
      have eff : PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun g =>
        g.inputs.take (bif g.op.eval [false] then 1 else 2)
      have rd : Fin n → List PEqualNP.CircuitLowerBounds.Gate := fun v =>
        C.gates.filter (fun g => (eff g).contains v.val)
      PEqualNP.MetaComplexity.IsMinimalCircuit n C →
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.circuitFun n C = F →
      (∀ v ∉ S, 1 ≤ (rd v).length ∧ (rd v).length ≤ 3 ∧ ((rd v).length = 3 → ∀ g ∈ rd v, g.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
      (∃ v ∉ S, ∃ g ∈ rd v, g.op = PEqualNP.CircuitLowerBounds.GateOp.and) →
      (∀ v ∉ S, ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
        C.gates[j]? = some g → g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.or →
        (eff g).contains v.val = true →
        (C.gates.drop (j + 1)).countP (fun h => (eff h).contains (n + j)) ≤ 2) →
      ∃ v ∉ S, ∃ s : ℕ, s + 4 ≤ C.size ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun x => F (Function.update x v false)) s)
    (hNotVertex : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ v ∉ S, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → 7 ≤ c.length) →
      (∀ u v : Fin n, G.Adj u v → u ∉ S) →
      (∃ u v : Fin n, G.Adj u v) →
      have F : (Fin n → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun G S
      have eff : PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun g =>
        g.inputs.take (bif g.op.eval [false] then 1 else 2)
      have rd : Fin n → List PEqualNP.CircuitLowerBounds.Gate := fun v =>
        C.gates.filter (fun g => (eff g).contains v.val)
      PEqualNP.MetaComplexity.IsMinimalCircuit n C →
      PEqualNP.MetaComplexity.circuitFun n C = F →
      (∀ v ∉ S, 1 ≤ (rd v).length ∧ (rd v).length ≤ 3 ∧ ((rd v).length = 3 → ∀ g ∈ rd v, g.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
      (∃ v ∉ S, ∃ g ∈ rd v, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
      (∀ v ∉ S, ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
        C.gates[j]? = some g → g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.or →
        (eff g).contains v.val = true →
        (C.gates.drop (j + 1)).countP (fun h => (eff h).contains (n + j)) ≤ 2) →
      ∃ v ∉ S, ∃ s : ℕ, s + 4 ≤ C.size ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun x => F (Function.update x v false)) s)
    (hNotOther : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ v ∉ S, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → 7 ≤ c.length) →
      (∀ u v : Fin n, G.Adj u v → u ∉ S) →
      (∃ u v : Fin n, G.Adj u v) →
      have F : (Fin n → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun G S
      have eff : PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun g =>
        g.inputs.take (bif g.op.eval [false] then 1 else 2)
      have rd : Fin n → List PEqualNP.CircuitLowerBounds.Gate := fun v =>
        C.gates.filter (fun g => (eff g).contains v.val)
      PEqualNP.MetaComplexity.IsMinimalCircuit n C →
      PEqualNP.MetaComplexity.circuitFun n C = F →
      (∀ v ∉ S, 1 ≤ (rd v).length ∧ (rd v).length ≤ 3 ∧ ((rd v).length = 3 → ∀ g ∈ rd v, g.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
      (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
      (∀ v ∉ S, ∀ g ∈ rd v, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) →
      (∀ v ∉ S, ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
        C.gates[j]? = some g → g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.or →
        (eff g).contains v.val = true →
        (C.gates.drop (j + 1)).countP (fun h => (eff h).contains (n + j)) ≤ 2) →
      ∃ v ∉ S, ∃ s : ℕ, s + 4 ≤ C.size ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun x => F (Function.update x v false)) s) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3,                       have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates;                       x16.length ≤ (3 : ℕ) ∧ (x16.length = (3 : ℕ) → ∀ x18 ∈ x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →                     ∃ x15 ∉ x3, ∃ (x16 : ℕ), x16 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x17 : Fin x1 → Bool) => x4 (Function.update x17 x15 Bool.false)) x16 := by
  intro n G S f C hdeg hgirth hAdjNS hHasEdge hf_spec hFan hFun hMinSz hRdBnd
  let _ : DecidableRel G.Adj := Classical.decRel G.Adj
  let F : (Fin n → Bool) → Bool := graphFun G S
  have hf_eq : f = F := by
    funext x
    rw [Bool.eq_iff_iff, hf_spec x]
    change _ ↔ (decide (∃ a ∈ S, x a = true) || decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) = true
    rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  subst hf_eq
  have hMin : IsMinimalCircuit n C :=
    ⟨hFan, fun D hDF hDeq => hMinSz D.size ⟨D, hDF, Nat.le_refl _, fun x => congrFun (hDeq.trans hFun) x⟩⟩
  let eff : Gate → List ℕ := fun g => g.inputs.take (bif g.op.eval [false] then 1 else 2)
  let rd : Fin n → List Gate := fun v => C.gates.filter (fun g => (eff g).contains v.val)
  let step : List Bool → Gate → List Bool := fun ws g =>
    ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  let run : List Gate → List Bool → List Bool := fun gs ws => gs.foldl step ws
  have hand_eval0 : GateOp.and.eval [] = true := rfl
  have hand_eval1 (a : Bool) : GateOp.and.eval [a] = a := by change (a && true) = a; exact Bool.and_true a
  have hand_eval2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
    change (a && (b && true)) = (a && b); exact congrArg (a && ·) (Bool.and_true b)
  have hor_eval0 : GateOp.or.eval [] = false := rfl
  have hor_eval1 (a : Bool) : GateOp.or.eval [a] = a := by change (a || false) = a; exact Bool.or_false a
  have hor_eval2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
    change (a || (b || false)) = (a || b); exact congrArg (a || ·) (Bool.or_false b)
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
  have run_snoc (gs : List Gate) (g : Gate) (ws : List Bool) :
      run (gs ++ [g]) ws = step (run gs ws) g := by
    simp only [run, List.foldl_append, List.foldl_cons, List.foldl_nil]
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
  have heff_eval (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
      (val : ℕ → Bool) :
      g.op.eval (g.inputs.map val) = g.op.eval ((eff g).map val) := by
    rcases hg.1 with hop | hop | hop
    · have htake : eff g = g.inputs := by
        dsimp only [eff]; rw [hop]
        have hf0 : GateOp.and.eval [false] = false := rfl
        rw [hf0]
        exact List.take_of_length_le hg.2
      rw [htake]
    · have htake : eff g = g.inputs := by
        dsimp only [eff]; rw [hop]
        have hf0 : GateOp.or.eval [false] = false := rfl
        rw [hf0]
        exact List.take_of_length_le hg.2
      rw [htake]
    · have htake : eff g = g.inputs.take 1 := by
        dsimp only [eff]; rw [hop]
        have hf0 : GateOp.not.eval [false] = true := rfl
        rw [hf0]
        rfl
      rw [htake, hop]
      cases g.inputs with
      | nil => rfl
      | cons a rest => rfl
  have heff_len (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
      (g.op = GateOp.not → (eff g).length ≤ 1) ∧ (eff g).length ≤ 2 := by
    constructor
    · intro hnot
      dsimp only [eff]; rw [hnot]
      have hf0 : GateOp.not.eval [false] = true := rfl
      rw [hf0]
      simp only [List.length_take, Bool.cond_true]
      omega
    · dsimp only [eff]
      simp only [List.length_take]
      omega
  have hRdPos : ∀ v ∉ S, 1 ≤ (rd v).length := by
    intro v hvS
    have hv_ncard : (G.neighborSet v).ncard = 3 := hdeg v hvS
    have hv_ne : (G.neighborSet v).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
    obtain ⟨w, hvw⟩ := hv_ne
    have hvw_adj : G.Adj v w := hvw
    have hwS : w ∉ S := hAdjNS w v hvw_adj.symm
    have hne_vw : w ≠ v := (G.ne_of_adj hvw_adj).symm
    let xw : Fin n → Bool := fun i => decide (i = w)
    let xvw : Fin n → Bool := Function.update xw v true
    have hF_single (u : Fin n) (huS : u ∉ S) : F (fun i => decide (i = u)) = false := by
      cases hval : F (fun i => decide (i = u))
      · rfl
      · exfalso
        rcases (hf_spec (fun i => decide (i = u))).mp hval with ⟨a, haS, hau⟩ | ⟨a, b, hab, hau, hbu⟩
        · have heq : a = u := by simpa only [decide_eq_true_eq] using hau
          subst heq; exact huS haS
        · have ha : a = u := by simpa only [decide_eq_true_eq] using hau
          have hb : b = u := by simpa only [decide_eq_true_eq] using hbu
          subst ha; subst hb
          exact G.loopless.irrefl _ hab
    have hF_xw : F xw = false := hF_single w hwS
    have hF_xvw : F xvw = true := by
      rw [hf_spec xvw]
      refine Or.inr ⟨v, w, hvw_adj, Function.update_self v true xw, ?_⟩
      dsimp only [xvw]
      rw [Function.update_of_ne hne_vw]
      simp only [xw, decide_true]
    have hout_nev : C.output ≠ v.val := by
      intro houtv
      let xv : Fin n → Bool := fun i => decide (i = v)
      have hev : circuitFun n C xv = true := by
        change (run C.gates (List.ofFn xv)).getD C.output false = true
        have hlt : v.val < (List.ofFn xv).length := by simp only [List.length_ofFn]; exact v.isLt
        rw [houtv, run_keep C.gates (List.ofFn xv) v.val hlt, List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
        simp only [xv, Fin.eta, decide_true]
      have hfx : circuitFun n C xv = F xv := congrFun hFun xv
      rw [hev, hF_single v hvS] at hfx
      cases hfx
    by_contra hlt1
    have hlen0 : (rd v).length = 0 := by omega
    have hnov : ∀ g ∈ C.gates, v.val ∉ eff g := by
      intro g hg hvmem
      have hmem : g ∈ rd v := List.mem_filter.mpr ⟨hg, List.elem_eq_true_of_mem hvmem⟩
      have hpos : 0 < (rd v).length := List.length_pos_of_mem hmem
      omega
    have hAgree (gs : List Gate) (hgsF : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
        (hgsV : ∀ g ∈ gs, v.val ∉ eff g) (wA wB : List Bool) (hlen : wA.length = wB.length)
        (hag : ∀ i, i ≠ v.val → wA.getD i false = wB.getD i false) :
        ∀ i, i ≠ v.val → (run gs wA).getD i false = (run gs wB).getD i false := by
      induction gs generalizing wA wB with
      | nil => exact hag
      | cons g rest ih =>
        simp only [run, List.foldl_cons] at ih ⊢
        have hgF := hgsF g List.mem_cons_self
        have hgV := hgsV g List.mem_cons_self
        have hbit : g.op.eval (g.inputs.map fun i => wA.getD i false) = g.op.eval (g.inputs.map fun i => wB.getD i false) := by
          rw [heff_eval g hgF (fun i => wA.getD i false), heff_eval g hgF (fun i => wB.getD i false)]
          congr 1
          apply List.map_congr_left
          intro i hi
          exact hag i (fun h => hgV (h ▸ hi))
        apply ih (fun g' hg' => hgsF g' (List.mem_cons_of_mem g hg'))
          (fun g' hg' => hgsV g' (List.mem_cons_of_mem g hg')) (step wA g) (step wB g)
        · simp only [step, List.length_append, List.length_cons, List.length_nil, hlen]
        · intro i hiv
          dsimp only [step]
          rw [hbit]
          by_cases heq : i = wA.length
          · subst heq; rw [getD_snoc_eq wA _, hlen, getD_snoc_eq wB _]
          · have heq2 : i ≠ wB.length := by rw [← hlen]; exact heq
            rw [getD_snoc_ne wA _ i heq, getD_snoc_ne wB _ i heq2]
            exact hag i hiv
    have hbase : ∀ i, i ≠ v.val → (List.ofFn xw).getD i false = (List.ofFn xvw).getD i false := by
      intro i hiv
      by_cases hi : i < n
      · have hlt1 : i < (List.ofFn xw).length := by simp only [List.length_ofFn]; exact hi
        have hlt2 : i < (List.ofFn xvw).length := by simp only [List.length_ofFn]; exact hi
        rw [List.getD_eq_getElem _ _ hlt1, List.getElem_ofFn, List.getD_eq_getElem _ _ hlt2, List.getElem_ofFn]
        dsimp only [xvw]
        rw [Function.update_of_ne (fun h => hiv (congrArg Fin.val h))]
      · rw [List.getD_eq_default (List.ofFn xw) false (n := i) (by simp only [List.length_ofFn]; omega),
            List.getD_eq_default (List.ofFn xvw) false (n := i) (by simp only [List.length_ofFn]; omega)]
    have hev_eq : circuitFun n C xw = circuitFun n C xvw :=
      hAgree C.gates hFan hnov (List.ofFn xw) (List.ofFn xvw) (by simp only [List.length_ofFn]) hbase C.output hout_nev
    rw [congrFun hFun xw, congrFun hFun xvw, hF_xw, hF_xvw] at hev_eq
    cases hev_eq
  have hRdAll : ∀ v ∉ S, 1 ≤ (rd v).length ∧ (rd v).length ≤ 3 ∧
      ((rd v).length = 3 → ∀ g ∈ rd v, g.op = GateOp.or) := by
    intro v hvS
    have hb := hRdBnd v hvS
    exact ⟨hRdPos v hvS, hb.1, hb.2⟩
  by_cases hHighOut : ∃ v ∉ S, ∃ (j0 : ℕ) (g0 : Gate),
      C.gates[j0]? = some g0 ∧ g0.op ≠ GateOp.or ∧ (eff g0).contains v.val = true ∧
      3 ≤ (C.gates.drop (j0 + 1)).countP (fun h => (eff h).contains (n + j0))
  · obtain ⟨v, hvS, j0, g0, hj0_get, hg0_ne_or, hg0_hasV, hcnt3⟩ := hHighOut
    have hj0_lt : j0 < C.gates.length := ((List.getElem?_eq_some_iff).mp hj0_get).1
    have hg0_eq : C.gates[j0]'hj0_lt = g0 := ((List.getElem?_eq_some_iff).mp hj0_get).2
    let updV : (Fin n → Bool) → Fin n → Bool := fun x => Function.update x v false
    let saved : ℕ → ℕ := fun k =>
      (if j0 < k then 1 else 0) + ((C.gates.take k).drop (j0 + 1)).countP (fun h => (eff h).contains (n + j0))
    have hCompile : ∀ k ≤ C.gates.length, ∃ gs : List Gate,
        gs.length + saved k ≤ k ∧
        (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
        (j0 < k → ∃ c0 : Bool, ∀ x : Fin n → Bool, (run C.gates (List.ofFn (updV x))).getD (n + j0) false = c0) ∧
        ∀ i < n + k,
          (∃ c : Bool, ∀ x : Fin n → Bool, (run C.gates (List.ofFn (updV x))).getD i false = c) ∨
          (∃ w < n + gs.length, ∀ x : Fin n → Bool, (run C.gates (List.ofFn (updV x))).getD i false = (run gs (List.ofFn x)).getD w false) := by
      intro k
      induction k with
      | zero =>
        intro _
        refine ⟨[], by simp only [saved, List.take_zero, List.drop_nil, List.countP_nil, List.length_nil, Nat.not_lt_zero, ↓reduceIte, Nat.add_zero, Nat.le_refl],
          (fun g hg => by cases hg), (fun h => by omega), ?_⟩
        intro i hi
        have hin : i < n := by omega
        by_cases hiv : i = v.val
        · subst hiv
          refine Or.inl ⟨false, fun x => ?_⟩
          have hlt : v.val < (List.ofFn (updV x)).length := by simp only [List.length_ofFn]; exact v.isLt
          rw [run_keep C.gates (List.ofFn (updV x)) v.val hlt, List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
          simp only [updV, Fin.eta, Function.update_self]
        · refine Or.inr ⟨i, by simp only [List.length_nil]; omega, fun x => ?_⟩
          have hlt1 : i < (List.ofFn (updV x)).length := by simp only [List.length_ofFn]; exact hin
          have hlt2 : i < (List.ofFn x).length := by simp only [List.length_ofFn]; exact hin
          rw [run_keep C.gates (List.ofFn (updV x)) i hlt1, List.getD_eq_getElem _ _ hlt1, List.getElem_ofFn]
          change updV x ⟨i, hin⟩ = (List.ofFn x).getD i false
          rw [List.getD_eq_getElem _ _ hlt2, List.getElem_ofFn]
          dsimp only [updV]
          rw [Function.update_of_ne (fun h => hiv (congrArg Fin.val h))]
      | succ k ih =>
        intro hk1
        obtain ⟨gs, hlen_sv, hgsF, hc0_ih, hmap⟩ := ih (by omega)
        let g : Gate := C.gates[k]'(by omega)
        have hg_mem : g ∈ C.gates := List.getElem_mem (by omega)
        have hgF := hFan g hg_mem
        have hwire_k (x : Fin n → Bool) :
            (run C.gates (List.ofFn (updV x))).getD (n + k) false =
              g.op.eval ((eff g).map fun i => (run (C.gates.take k) (List.ofFn (updV x))).getD i false) := by
          have hsp : C.gates = C.gates.take k ++ [g] ++ C.gates.drop (k + 1) := by
            have h2 : C.gates.drop k = g :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons (by omega)
            calc C.gates = C.gates.take k ++ C.gates.drop k := (List.take_append_drop k C.gates).symm
              _ = C.gates.take k ++ (g :: C.gates.drop (k + 1)) := by rw [h2]
              _ = C.gates.take k ++ [g] ++ C.gates.drop (k + 1) := by rw [List.append_assoc, List.singleton_append]
          conv_lhs => rw [hsp, run_append, run_append]
          have hlen1 : (run (C.gates.take k) (List.ofFn (updV x))).length = n + k := by
            rw [run_len, List.length_ofFn, List.length_take]; omega
          have hlt2 : n + k < (run [g] (run (C.gates.take k) (List.ofFn (updV x)))).length := by
            rw [run_len, hlen1, List.length_cons, List.length_nil]; omega
          rw [run_keep (C.gates.drop (k + 1)) _ (n + k) hlt2]
          change (step (run (C.gates.take k) (List.ofFn (updV x))) g).getD (n + k) false = _
          dsimp only [step]
          rw [← hlen1, getD_snoc_eq (run (C.gates.take k) (List.ofFn (updV x))) _]
          exact heff_eval g hgF (fun i => (run (C.gates.take k) (List.ofFn (updV x))).getD i false)
        have hpre_eq (x : Fin n → Bool) (i : ℕ) (hi : i < n + k) :
            (run (C.gates.take k) (List.ofFn (updV x))).getD i false = (run C.gates (List.ofFn (updV x))).getD i false := by
          have hsp : C.gates = C.gates.take k ++ C.gates.drop k := (List.take_append_drop k C.gates).symm
          conv_rhs => rw [hsp, run_append]
          exact (run_keep (C.gates.drop k) (run (C.gates.take k) (List.ofFn (updV x))) i
            (by rw [run_len, List.length_ofFn, List.length_take]; omega)).symm
        have hMapIn (i : ℕ) :
            (∃ c : Bool, ∀ x : Fin n → Bool, (run (C.gates.take k) (List.ofFn (updV x))).getD i false = c) ∨
            (∃ w < n + gs.length, ∀ x : Fin n → Bool, (run (C.gates.take k) (List.ofFn (updV x))).getD i false = (run gs (List.ofFn x)).getD w false) := by
          by_cases hi : i < n + k
          · rcases hmap i hi with ⟨c, hc⟩ | ⟨w, hw, hww⟩
            · exact Or.inl ⟨c, fun x => (hpre_eq x i hi).trans (hc x)⟩
            · exact Or.inr ⟨w, hw, fun x => (hpre_eq x i hi).trans (hww x)⟩
          · refine Or.inl ⟨false, fun x => ?_⟩
            exact List.getD_eq_default _ false (n := i) (by rw [run_len, List.length_ofFn, List.length_take]; omega)
        have hsaved_step : saved (k + 1) = saved k +
            (if k = j0 then 1 else if j0 < k ∧ (eff g).contains (n + j0) = true then 1 else 0) := by
          have htake : C.gates.take (k + 1) = C.gates.take k ++ [g] := List.take_succ_eq_append_getElem (by omega)
          by_cases hk_lt : k < j0
          · have h1 : ¬ (j0 < k) := by omega
            have h2 : ¬ (j0 < k + 1) := by omega
            have h3 : k ≠ j0 := by omega
            have hd1 : (C.gates.take k).drop (j0 + 1) = [] :=
              List.drop_eq_nil_of_le (by simp only [List.length_take]; omega)
            have hd2 : (C.gates.take (k + 1)).drop (j0 + 1) = [] :=
              List.drop_eq_nil_of_le (by simp only [List.length_take]; omega)
            simp only [saved, h1, h2, h3, hd1, hd2, List.countP_nil, false_and, ↓reduceIte]
          · by_cases hk_eq : k = j0
            · subst hk_eq
              have h1 : ¬ (k < k) := by omega
              have h2 : k < k + 1 := by omega
              have hd1 : (C.gates.take k).drop (k + 1) = [] :=
                List.drop_eq_nil_of_le (by simp only [List.length_take]; omega)
              have hd2 : (C.gates.take (k + 1)).drop (k + 1) = [] :=
                List.drop_eq_nil_of_le (by simp only [List.length_take]; omega)
              simp only [saved, h1, h2, hd1, hd2, List.countP_nil, ↓reduceIte]
            · have hk_gt : j0 < k := by omega
              have hk1_gt : j0 < k + 1 := by omega
              have hdrop : (C.gates.take (k + 1)).drop (j0 + 1) = (C.gates.take k).drop (j0 + 1) ++ [g] := by
                rw [htake, List.drop_append_of_le_length (by simp only [List.length_take]; omega)]
              simp only [saved, hk_gt, hk1_gt, hk_eq, hdrop, List.countP_append, List.countP_cons, List.countP_nil, true_and, ↓reduceIte]
              cases (eff g).contains (n + j0) <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
        have hNoEmit (hnew :
            (∃ c : Bool, ∀ x : Fin n → Bool, (run C.gates (List.ofFn (updV x))).getD (n + k) false = c) ∨
            (∃ w < n + gs.length, ∀ x : Fin n → Bool, (run C.gates (List.ofFn (updV x))).getD (n + k) false = (run gs (List.ofFn x)).getD w false))
            (hc0' : j0 < k + 1 → ∃ c0 : Bool, ∀ x : Fin n → Bool, (run C.gates (List.ofFn (updV x))).getD (n + j0) false = c0) :
            ∃ gs' : List Gate, gs'.length + saved (k + 1) ≤ k + 1 ∧
              (∀ g' ∈ gs', g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2) ∧
              (j0 < k + 1 → ∃ c0 : Bool, ∀ x : Fin n → Bool, (run C.gates (List.ofFn (updV x))).getD (n + j0) false = c0) ∧
              ∀ i < n + (k + 1),
                (∃ c : Bool, ∀ x : Fin n → Bool, (run C.gates (List.ofFn (updV x))).getD i false = c) ∨
                (∃ w < n + gs'.length, ∀ x : Fin n → Bool, (run C.gates (List.ofFn (updV x))).getD i false = (run gs' (List.ofFn x)).getD w false) := by
          refine ⟨gs, ?_, hgsF, hc0', ?_⟩
          · rw [hsaved_step]
            split_ifs <;> omega
          · intro i hi
            by_cases heq : i = n + k
            · subst heq; exact hnew
            · exact hmap i (by omega)
        have hCanEmit (hop_not_j0 : k ≠ j0) (hnot_use : ¬ (j0 < k ∧ (eff g).contains (n + j0) = true))
            (gNew : Gate) (hgNewF : gNew.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ gNew.inputs.length ≤ 2)
            (hgNew_eq : ∀ x : Fin n → Bool, (run C.gates (List.ofFn (updV x))).getD (n + k) false =
              gNew.op.eval (gNew.inputs.map fun idx => (run gs (List.ofFn x)).getD idx false)) :
            ∃ gs' : List Gate, gs'.length + saved (k + 1) ≤ k + 1 ∧
              (∀ g' ∈ gs', g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2) ∧
              (j0 < k + 1 → ∃ c0 : Bool, ∀ x : Fin n → Bool, (run C.gates (List.ofFn (updV x))).getD (n + j0) false = c0) ∧
              ∀ i < n + (k + 1),
                (∃ c : Bool, ∀ x : Fin n → Bool, (run C.gates (List.ofFn (updV x))).getD i false = c) ∨
                (∃ w < n + gs'.length, ∀ x : Fin n → Bool, (run C.gates (List.ofFn (updV x))).getD i false = (run gs' (List.ofFn x)).getD w false) := by
          refine ⟨gs ++ [gNew], ?_, ?_, ?_, ?_⟩
          · rw [hsaved_step]
            simp only [hop_not_j0, hnot_use, ↓reduceIte, List.length_append, List.length_cons, List.length_nil]
            omega
          · intro g' hg'
            rw [List.mem_append, List.mem_singleton] at hg'
            rcases hg' with hg' | rfl
            · exact hgsF g' hg'
            · exact hgNewF
          · intro hlt
            exact hc0_ih (by omega)
          · intro i hi
            by_cases heq : i = n + k
            · subst heq
              refine Or.inr ⟨n + gs.length, by simp only [List.length_append, List.length_cons, List.length_nil]; omega, fun x => ?_⟩
              rw [hgNew_eq x, run_snoc]
              have hlen_run : (run gs (List.ofFn x)).length = n + gs.length := by rw [run_len, List.length_ofFn]
              dsimp only [step]
              rw [← hlen_run, getD_snoc_eq (run gs (List.ofFn x)) _]
            · rcases hmap i (by omega) with ⟨c, hc⟩ | ⟨w, hw, hww⟩
              · exact Or.inl ⟨c, hc⟩
              · refine Or.inr ⟨w, by simp only [List.length_append, List.length_cons, List.length_nil]; omega, fun x => ?_⟩
                rw [hww x, run_snoc]
                have hlen_run : (run gs (List.ofFn x)).length = n + gs.length := by rw [run_len, List.length_ofFn]
                exact (getD_snoc_ne (run gs (List.ofFn x)) _ w (by omega)).symm
        have hc0_const_if_k (c : Bool) (hc : ∀ x : Fin n → Bool, (run C.gates (List.ofFn (updV x))).getD (n + k) false = c) :
            j0 < k + 1 → ∃ c0 : Bool, ∀ x : Fin n → Bool, (run C.gates (List.ofFn (updV x))).getD (n + j0) false = c0 := by
          intro hlt
          by_cases hkj : k = j0
          · subst hkj; exact ⟨c, hc⟩
          · exact hc0_ih (by omega)
        have hConstArg (a : ℕ) (ha_mem : a ∈ eff g) (ha_const : ∃ ca : Bool, ∀ x : Fin n → Bool, (run (C.gates.take k) (List.ofFn (updV x))).getD a false = ca) :
            (k = j0 → ∃ ck : Bool, ∀ x : Fin n → Bool, (run C.gates (List.ofFn (updV x))).getD (n + k) false = ck) →
            ∃ gs' : List Gate, gs'.length + saved (k + 1) ≤ k + 1 ∧
              (∀ g' ∈ gs', g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2) ∧
              (j0 < k + 1 → ∃ c0 : Bool, ∀ x : Fin n → Bool, (run C.gates (List.ofFn (updV x))).getD (n + j0) false = c0) ∧
              ∀ i < n + (k + 1),
                (∃ c : Bool, ∀ x : Fin n → Bool, (run C.gates (List.ofFn (updV x))).getD i false = c) ∨
                (∃ w < n + gs'.length, ∀ x : Fin n → Bool, (run C.gates (List.ofFn (updV x))).getD i false = (run gs' (List.ofFn x)).getD w false) := by
          intro hk_j0_const
          obtain ⟨ca, hca⟩ := ha_const
          have hc0_out : j0 < k + 1 → ∃ c0 : Bool, ∀ x : Fin n → Bool, (run C.gates (List.ofFn (updV x))).getD (n + j0) false = c0 := by
            intro hlt
            by_cases hkj : k = j0
            · obtain ⟨ck, hck⟩ := hk_j0_const hkj
              rw [hkj] at hck
              exact ⟨ck, hck⟩
            · exact hc0_ih (by omega)
          have hlen2 := (heff_len g hgF).2
          cases heff : eff g with
          | nil => rw [heff] at ha_mem; cases ha_mem
          | cons i1 rest =>
            cases rest with
            | nil =>
              rw [heff, List.mem_singleton] at ha_mem
              subst ha_mem
              apply hNoEmit _ hc0_out
              refine Or.inl ⟨g.op.eval [ca], fun x => ?_⟩
              rw [hwire_k x, heff, List.map_cons, List.map_nil, hca x]
            | cons i2 rest2 =>
              cases rest2 with
              | nil =>
                rw [heff, List.mem_cons, List.mem_singleton] at ha_mem
                rcases hgF.1 with hand | hor | hnot
                · have hcase (x_val y_val : ℕ) (hxy : eff g = [x_val, y_val] ∨ eff g = [y_val, x_val])
                      (hcx : ∀ x : Fin n → Bool, (run (C.gates.take k) (List.ofFn (updV x))).getD x_val false = ca) :
                      (∃ c : Bool, ∀ x : Fin n → Bool, (run C.gates (List.ofFn (updV x))).getD (n + k) false = c) ∨
                      (∃ w < n + gs.length, ∀ x : Fin n → Bool, (run C.gates (List.ofFn (updV x))).getD (n + k) false = (run gs (List.ofFn x)).getD w false) := by
                    cases ca
                    · refine Or.inl ⟨false, fun x => ?_⟩
                      rw [hwire_k x, hand]
                      rcases hxy with h | h <;> rw [h, List.map_cons, List.map_cons, List.map_nil, hand_eval2, hcx x]
                      · exact Bool.false_and _
                      · exact Bool.and_false _
                    · rcases hMapIn y_val with ⟨cy, hcy⟩ | ⟨wy, hwy, hwwy⟩
                      · refine Or.inl ⟨cy, fun x => ?_⟩
                        rw [hwire_k x, hand]
                        rcases hxy with h | h <;> rw [h, List.map_cons, List.map_cons, List.map_nil, hand_eval2, hcx x, hcy x]
                        · exact Bool.true_and _
                        · exact Bool.and_true _
                      · refine Or.inr ⟨wy, hwy, fun x => ?_⟩
                        rw [hwire_k x, hand]
                        rcases hxy with h | h <;> rw [h, List.map_cons, List.map_cons, List.map_nil, hand_eval2, hcx x, hwwy x]
                        · exact Bool.true_and _
                        · exact Bool.and_true _
                  apply hNoEmit _ hc0_out
                  rcases ha_mem with rfl | rfl
                  · exact hcase a i2 (Or.inl heff) hca
                  · exact hcase a i1 (Or.inr heff) hca
                · have hcase (x_val y_val : ℕ) (hxy : eff g = [x_val, y_val] ∨ eff g = [y_val, x_val])
                      (hcx : ∀ x : Fin n → Bool, (run (C.gates.take k) (List.ofFn (updV x))).getD x_val false = ca) :
                      (∃ c : Bool, ∀ x : Fin n → Bool, (run C.gates (List.ofFn (updV x))).getD (n + k) false = c) ∨
                      (∃ w < n + gs.length, ∀ x : Fin n → Bool, (run C.gates (List.ofFn (updV x))).getD (n + k) false = (run gs (List.ofFn x)).getD w false) := by
                    cases ca
                    · rcases hMapIn y_val with ⟨cy, hcy⟩ | ⟨wy, hwy, hwwy⟩
                      · refine Or.inl ⟨cy, fun x => ?_⟩
                        rw [hwire_k x, hor]
                        rcases hxy with h | h <;> rw [h, List.map_cons, List.map_cons, List.map_nil, hor_eval2, hcx x, hcy x]
                        · exact Bool.false_or _
                        · exact Bool.or_false _
                      · refine Or.inr ⟨wy, hwy, fun x => ?_⟩
                        rw [hwire_k x, hor]
                        rcases hxy with h | h <;> rw [h, List.map_cons, List.map_cons, List.map_nil, hor_eval2, hcx x, hwwy x]
                        · exact Bool.false_or _
                        · exact Bool.or_false _
                    · refine Or.inl ⟨true, fun x => ?_⟩
                      rw [hwire_k x, hor]
                      rcases hxy with h | h <;> rw [h, List.map_cons, List.map_cons, List.map_nil, hor_eval2, hcx x]
                      · exact Bool.true_or _
                      · exact Bool.or_true _
                  apply hNoEmit _ hc0_out
                  rcases ha_mem with rfl | rfl
                  · exact hcase a i2 (Or.inl heff) hca
                  · exact hcase a i1 (Or.inr heff) hca
                · have hlen1 := (heff_len g hgF).1 hnot
                  rw [heff] at hlen1
                  simp only [List.length_cons, List.length_nil] at hlen1
                  omega
              | cons _ _ =>
                rw [heff] at hlen2
                simp only [List.length_cons] at hlen2
                omega
        by_cases hkj0 : k = j0
        · have hg_is_g0 : g = g0 := by dsimp only [g]; subst hkj0; exact hg0_eq
          have hv_in : v.val ∈ eff g := by rw [hg_is_g0]; exact List.mem_of_elem_eq_true hg0_hasV
          have hv_const : ∀ x : Fin n → Bool, (run (C.gates.take k) (List.ofFn (updV x))).getD v.val false = false := by
            intro x
            have hlt : v.val < (List.ofFn (updV x)).length := by simp only [List.length_ofFn]; exact v.isLt
            rw [run_keep _ _ v.val hlt, List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
            simp only [updV, Fin.eta, Function.update_self]
          apply hConstArg v.val hv_in ⟨false, hv_const⟩
          intro _
          rcases hgF.1 with hand | hor | hnot
          · refine ⟨false, fun x => ?_⟩
            rw [hwire_k x, hand]
            change ((eff g).map fun i => (run (C.gates.take k) (List.ofFn (updV x))).getD i false).all id = false
            cases hall : ((eff g).map fun i => (run (C.gates.take k) (List.ofFn (updV x))).getD i false).all id
            · rfl
            · rw [List.all_eq_true] at hall
              have htrue := hall ((run (C.gates.take k) (List.ofFn (updV x))).getD v.val false) (List.mem_map_of_mem hv_in)
              rw [hv_const x] at htrue
              cases htrue
          · rw [hg_is_g0] at hor; exact absurd hor hg0_ne_or
          · have hlen1 := (heff_len g hgF).1 hnot
            cases heff : eff g with
            | nil => rw [heff] at hv_in; cases hv_in
            | cons a rest =>
              cases rest with
              | nil =>
                rw [heff, List.mem_singleton] at hv_in
                subst hv_in
                refine ⟨true, fun x => ?_⟩
                rw [hwire_k x, hnot, heff, List.map_cons, List.map_nil, hv_const x]
                rfl
              | cons _ _ =>
                rw [heff] at hlen1
                simp only [List.length_cons] at hlen1
                omega
        · by_cases huse : j0 < k ∧ (eff g).contains (n + j0) = true
          · obtain ⟨c0, hc0⟩ := hc0_ih huse.1
            have hj0_in : n + j0 ∈ eff g := List.mem_of_elem_eq_true huse.2
            have hj0_const : ∀ x : Fin n → Bool, (run (C.gates.take k) (List.ofFn (updV x))).getD (n + j0) false = c0 :=
              fun x => (hpre_eq x (n + j0) (by omega)).trans (hc0 x)
            exact hConstArg (n + j0) hj0_in ⟨c0, hj0_const⟩ (fun h => absurd h hkj0)
          · have hlen2 := (heff_len g hgF).2
            cases heff : eff g with
            | nil =>
              have hc : ∀ x : Fin n → Bool, (run C.gates (List.ofFn (updV x))).getD (n + k) false = g.op.eval [] := by
                intro x; rw [hwire_k x, heff, List.map_nil]
              exact hNoEmit (Or.inl ⟨g.op.eval [], hc⟩) (hc0_const_if_k (g.op.eval []) hc)
            | cons i1 rest =>
              cases rest with
              | nil =>
                rcases hMapIn i1 with ⟨c1, hc1⟩ | ⟨w1, hw1, hww1⟩
                · exact hConstArg i1 (by rw [heff]; exact List.mem_cons_self) ⟨c1, hc1⟩ (fun h => absurd h hkj0)
                · rcases hgF.1 with hand | hor | hnot
                  · apply hNoEmit _ (fun hlt => hc0_ih (by omega))
                    refine Or.inr ⟨w1, hw1, fun x => ?_⟩
                    rw [hwire_k x, hand, heff, List.map_cons, List.map_nil, hand_eval1, hww1 x]
                  · apply hNoEmit _ (fun hlt => hc0_ih (by omega))
                    refine Or.inr ⟨w1, hw1, fun x => ?_⟩
                    rw [hwire_k x, hor, heff, List.map_cons, List.map_nil, hor_eval1, hww1 x]
                  · apply hCanEmit hkj0 huse ⟨GateOp.not, [w1]⟩ ⟨Or.inr (Or.inr rfl), by simp only [List.length_cons, List.length_nil]; omega⟩
                    intro x
                    rw [hwire_k x, hnot, heff, List.map_cons, List.map_nil, List.map_cons, List.map_nil, hww1 x]
              | cons i2 rest2 =>
                cases rest2 with
                | nil =>
                  rcases hMapIn i1 with ⟨c1, hc1⟩ | ⟨w1, hw1, hww1⟩
                  · exact hConstArg i1 (by rw [heff]; exact List.mem_cons_self) ⟨c1, hc1⟩ (fun h => absurd h hkj0)
                  · rcases hMapIn i2 with ⟨c2, hc2⟩ | ⟨w2, hw2, hww2⟩
                    · exact hConstArg i2 (by rw [heff]; exact List.mem_cons_of_mem i1 List.mem_cons_self) ⟨c2, hc2⟩ (fun h => absurd h hkj0)
                    · apply hCanEmit hkj0 huse ⟨g.op, [w1, w2]⟩ ⟨hgF.1, by simp only [List.length_cons, List.length_nil]; omega⟩
                      intro x
                      rw [hwire_k x, heff, List.map_cons, List.map_cons, List.map_nil, List.map_cons, List.map_cons, List.map_nil, hww1 x, hww2 x]
                | cons _ _ =>
                  rw [heff] at hlen2
                  simp only [List.length_cons] at hlen2
                  omega
    obtain ⟨gs, hlen_sv, hgsF, _, hmap⟩ := hCompile C.gates.length (Nat.le_refl _)
    have hsaved_ge4 : 4 ≤ saved C.gates.length := by
      dsimp only [saved]
      rw [List.take_length]
      simp only [hj0_lt, ↓reduceIte]
      omega
    have hgs_le : gs.length + 4 ≤ C.size := by
      change gs.length + 4 ≤ C.gates.length
      omega
    have hF_allFalse : F (fun _ => false) = false := by
      cases hval : F (fun _ => false)
      · rfl
      · exfalso
        rcases (hf_spec (fun _ => false)).mp hval with ⟨_, _, h⟩ | ⟨_, _, _, h, _⟩ <;> cases h
    by_cases hout_lt : C.output < n + C.gates.length
    · rcases hmap C.output hout_lt with ⟨c, hc⟩ | ⟨w, _, hww⟩
      · cases c
        · refine ⟨v, hvS, 0, by omega, ⟨⟨[], n⟩, (fun g hg => by cases hg), Nat.le_refl 0, fun x => ?_⟩⟩
          change (List.ofFn x).getD n false = F (updV x)
          rw [List.getD_eq_default (List.ofFn x) false (n := n) (by simp only [List.length_ofFn]; omega)]
          have h1 : (run C.gates (List.ofFn (updV x))).getD C.output false = false := hc x
          have h2 : (run C.gates (List.ofFn (updV x))).getD C.output false = F (updV x) := congrFun hFun (updV x)
          exact h1.symm.trans h2
        · exfalso
          have h1 : (run C.gates (List.ofFn (updV (fun _ => false)))).getD C.output false = true := hc (fun _ => false)
          have h2 : (run C.gates (List.ofFn (updV (fun _ => false)))).getD C.output false = F (updV (fun _ => false)) :=
            congrFun hFun (updV (fun _ => false))
          have hupd0 : updV (fun _ => false) = fun _ => false := by
            funext i
            dsimp only [updV]
            by_cases hi : i = v
            · subst i; exact Function.update_self v false (fun _ => false)
            · exact Function.update_of_ne hi false (fun _ => false)
          rw [hupd0, hF_allFalse] at h2
          rw [hupd0] at h1
          rw [h1] at h2
          cases h2
      · refine ⟨v, hvS, gs.length, hgs_le, ⟨⟨gs, w⟩, hgsF, Nat.le_refl _, fun x => ?_⟩⟩
        change (run gs (List.ofFn x)).getD w false = F (updV x)
        rw [← hww x]
        exact congrFun hFun (updV x)
    · refine ⟨v, hvS, 0, by omega, ⟨⟨[], n⟩, (fun g hg => by cases hg), Nat.le_refl 0, fun x => ?_⟩⟩
      change (List.ofFn x).getD n false = F (updV x)
      rw [List.getD_eq_default (List.ofFn x) false (n := n) (by simp only [List.length_ofFn]; omega)]
      have h1 : (run C.gates (List.ofFn (updV x))).getD C.output false = false :=
        List.getD_eq_default _ false (n := C.output) (by rw [run_len, List.length_ofFn]; omega)
      have h2 : (run C.gates (List.ofFn (updV x))).getD C.output false = F (updV x) := congrFun hFun (updV x)
      exact h1.symm.trans h2
  · have hLowOut : ∀ v ∉ S, ∀ (j : ℕ) (g : Gate),
        C.gates[j]? = some g → g.op ≠ GateOp.or → (eff g).contains v.val = true →
        (C.gates.drop (j + 1)).countP (fun h => (eff h).contains (n + j)) ≤ 2 := by
      intro v hvS j g hj hgne hhas
      by_contra hgt
      exact hHighOut ⟨v, hvS, j, g, hj, hgne, hhas, by omega⟩
    by_cases hHasNot : ∃ g ∈ C.gates, g.op = GateOp.not
    · by_cases hNotV : ∃ v ∉ S, ∃ g ∈ rd v, g.op = GateOp.not
      · exact hNotVertex n G S C hdeg hgirth hAdjNS hHasEdge hMin hFun hRdAll hNotV hLowOut
      · have hNoNotV : ∀ v ∉ S, ∀ g ∈ rd v, g.op ≠ GateOp.not :=
          fun v hvS g hg hnot => hNotV ⟨v, hvS, g, hg, hnot⟩
        exact hNotOther n G S C hdeg hgirth hAdjNS hHasEdge hMin hFun hRdAll hHasNot hNoNotV hLowOut
    · have hMono : Monotone2 C := by
        intro g hg
        have hf := hFan g hg
        refine ⟨?_, hf.2⟩
        rcases hf.1 with hand | hor | hnot
        · exact Or.inl hand
        · exact Or.inr hor
        · exact absurd ⟨g, hg, hnot⟩ hHasNot
      by_cases hHasAndV : ∃ v ∉ S, ∃ g ∈ rd v, g.op = GateOp.and
      · exact hMonoHasAnd n G S C hdeg hgirth hAdjNS hHasEdge hMin hMono hFun hRdAll hHasAndV hLowOut
      · have hAllOr : ∀ v ∉ S, 1 ≤ (rd v).length ∧ (rd v).length ≤ 3 ∧ ∀ g ∈ rd v, g.op = GateOp.or := by
          intro v hvS
          have hb := hRdAll v hvS
          refine ⟨hb.1, hb.2.1, fun g hg => ?_⟩
          have hgC : g ∈ C.gates := (List.mem_filter.mp hg).1
          rcases (hMono g hgC).1 with hand | hor
          · exact absurd ⟨v, hvS, g, hg, hand⟩ hHasAndV
          · exact hor
        exact hMonoAllOr n G S C hdeg hgirth hAdjNS hHasEdge hMin hMono hFun hAllOr
