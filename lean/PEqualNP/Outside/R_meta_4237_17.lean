import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_4237_17
    (hHalfUnit : ∃ d c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v : Fin n, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      PEqualNP.EdgeOwnership.EveryEdgeOwned n G C →
      ∀ U ⊆ {e ∈ G.edgeFinset | ¬∃ (u v : Fin n), e = s(u, v) ∧ ∃ j : Fin C.gates.length, PEqualNP.EdgeOwnership.Owns n C j.val u v ∧ ∀ (a b : Fin n), PEqualNP.EdgeOwnership.gateVal n C j.val (PEqualNP.EdgeOwnership.pairInput a b) = true → G.Adj a b},
      U.Nonempty →
      (∀ v : Fin n, {e ∈ U | v ∈ e}.card = 0 ∨ d < {e ∈ U | v ∈ e}.card) →
      ∀ U' ⊆ U, U.card ≤ 2 * U'.card →
      (∀ e ∈ U', ∃ u v : Fin n, e = s(u, v) ∧ ∃ j : Fin C.gates.length, PEqualNP.EdgeOwnership.Owns n C j.val u v ∧ ∃ a : Fin n, PEqualNP.EdgeOwnership.gateVal n C j.val (PEqualNP.EdgeOwnership.pairInput a a) = true) →
      U.card ≤ c * (C.size + 1))
    (hStarNonEdge : ∃ d c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v : Fin n, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      PEqualNP.EdgeOwnership.EveryEdgeOwned n G C →
      PEqualNP.EdgeOwnership.HasStarProfile n G C →
      ∀ U ⊆ {e ∈ G.edgeFinset | ¬∃ (u v : Fin n), e = s(u, v) ∧ ∃ j : Fin C.gates.length, PEqualNP.EdgeOwnership.Owns n C j.val u v ∧ ∀ (a b : Fin n), PEqualNP.EdgeOwnership.gateVal n C j.val (PEqualNP.EdgeOwnership.pairInput a b) = true → G.Adj a b},
      U.Nonempty →
      (∀ v : Fin n, {e ∈ U | v ∈ e}.card = 0 ∨ d < {e ∈ U | v ∈ e}.card) →
      ∀ U' ⊆ U, U.card ≤ 2 * U'.card →
      (∀ e ∈ U', ∀ u v : Fin n, e = s(u, v) → ∀ j : Fin C.gates.length, PEqualNP.EdgeOwnership.Owns n C j.val u v → (∀ a : Fin n, PEqualNP.EdgeOwnership.gateVal n C j.val (PEqualNP.EdgeOwnership.pairInput a a) = false) ∧ ∃ a b : Fin n, a ≠ b ∧ ¬ G.Adj a b ∧ PEqualNP.EdgeOwnership.gateVal n C j.val (PEqualNP.EdgeOwnership.pairInput a b) = true) →
      U.card ≤ c * (C.size + 1))
    (hNonStarNonEdge : ∃ d c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v : Fin n, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      PEqualNP.EdgeOwnership.EveryEdgeOwned n G C →
      ¬ PEqualNP.EdgeOwnership.HasStarProfile n G C →
      ∀ U ⊆ {e ∈ G.edgeFinset | ¬∃ (u v : Fin n), e = s(u, v) ∧ ∃ j : Fin C.gates.length, PEqualNP.EdgeOwnership.Owns n C j.val u v ∧ ∀ (a b : Fin n), PEqualNP.EdgeOwnership.gateVal n C j.val (PEqualNP.EdgeOwnership.pairInput a b) = true → G.Adj a b},
      U.Nonempty →
      (∀ v : Fin n, {e ∈ U | v ∈ e}.card = 0 ∨ d < {e ∈ U | v ∈ e}.card) →
      ∀ U' ⊆ U, U.card ≤ 2 * U'.card →
      (∀ e ∈ U', ∀ u v : Fin n, e = s(u, v) → ∀ j : Fin C.gates.length, PEqualNP.EdgeOwnership.Owns n C j.val u v → (∀ a : Fin n, PEqualNP.EdgeOwnership.gateVal n C j.val (PEqualNP.EdgeOwnership.pairInput a a) = false) ∧ ∃ a b : Fin n, a ≠ b ∧ ¬ G.Adj a b ∧ PEqualNP.EdgeOwnership.gateVal n C j.val (PEqualNP.EdgeOwnership.pairInput a b) = true) →
      U.card ≤ c * (C.size + 1)) :
    ∃ (x1 : ℕ) (x2 : ℕ), ∀ (x3 : ℕ) (x4 : SimpleGraph (Fin x3)) [DecidableRel x4.Adj], (∀ (x6 : Fin x3), x4.degree x6 = (0 : ℕ) ∨ (3 : ℕ) ≤ x4.degree x6) → (∀ (x7 : Fin x3) (x8 : x4.Walk x7 x7), x8.IsCycle → (5 : ℕ) ≤ x8.length) → ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 → PEqualNP.MetaComplexity.circuitFun x3 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x4 ∅ → ∀ x11 ⊆ {x12 ∈ x4.edgeFinset | ¬∃ (x13 : Fin x3) (x14 : Fin x3), x12 = s(x13, x14) ∧ ∃ (x15 : Fin x8.gates.length), PEqualNP.EdgeOwnership.Owns x3 x8 (↑x15) x13 x14 ∧ ∀ (x16 x17 : Fin x3), PEqualNP.EdgeOwnership.gateVal x3 x8 (↑x15) (PEqualNP.EdgeOwnership.pairInput x16 x17) = Bool.true → x4.Adj x16 x17}, (∀ (x13 : Fin x3), {x14 ∈ x11 | x13 ∈ x14}.card = (0 : ℕ) ∨ x1 < {x14 ∈ x11 | x13 ∈ x14}.card) → x11.card ≤ x2 * (x8.size + (1 : ℕ)) := by
  obtain ⟨d1, c1, hc1⟩ := hHalfUnit
  obtain ⟨d2, c2, hc2⟩ := hStarNonEdge
  obtain ⟨d3, c3, hc3⟩ := hNonStarNonEdge
  refine ⟨max d1 (max d2 d3), max c1 (max c2 c3), ?_⟩
  intro n G hdec hdeg hgirth C hmono hfun U hUsub hUdeg
  by_cases hUne : U.Nonempty
  · let step : List Bool → Gate → List Bool := fun w g =>
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
    let wLe : List Bool → List Bool → Prop := fun w1 w2 =>
      w1.length = w2.length ∧ ∀ i, w1.getD i false = true → w2.getD i false = true
    have run_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
        ∀ w1 w2, wLe w1 w2 → wLe (run gs w1) (run gs w2) := by
      induction gs with
      | nil => intro w1 w2 h; exact h
      | cons g rest ih =>
        intro w1 w2 hle
        simp only [run, List.foldl_cons]
        apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))
        have hg := (hgs g List.mem_cons_self).1
        have hbit : g.op.eval (g.inputs.map fun i => w1.getD i false) = true →
            g.op.eval (g.inputs.map fun i => w2.getD i false) = true := by
          rcases hg with hop | hop
          · rw [hop]
            change (g.inputs.map fun i => w1.getD i false).all id = true →
              (g.inputs.map fun i => w2.getD i false).all id = true
            intro hall
            rw [List.all_eq_true] at hall ⊢
            intro b hb
            rw [List.mem_map] at hb
            obtain ⟨i, hi, rfl⟩ := hb
            exact hle.2 i (hall (w1.getD i false) (List.mem_map_of_mem hi))
          · rw [hop]
            change (g.inputs.map fun i => w1.getD i false).any id = true →
              (g.inputs.map fun i => w2.getD i false).any id = true
            intro hany
            rw [List.any_eq_true] at hany ⊢
            obtain ⟨b, hb, hbt⟩ := hany
            rw [List.mem_map] at hb
            obtain ⟨i, hi, rfl⟩ := hb
            exact ⟨w2.getD i false, List.mem_map_of_mem hi, hle.2 i hbt⟩
        refine ⟨by simp only [step, List.length_append, hle.1, List.length_cons, List.length_nil], ?_⟩
        intro i hi
        dsimp only [step] at hi ⊢
        by_cases heq : i = w1.length
        · subst heq
          rw [getD_snoc_eq w1 _ false] at hi
          rw [hle.1, getD_snoc_eq w2 _ false]
          exact hbit hi
        · have heq2 : i ≠ w2.length := by rw [← hle.1]; exact heq
          rw [getD_snoc_ne w1 _ false i heq] at hi
          rw [getD_snoc_ne w2 _ false i heq2]
          exact hle.2 i hi
    have hgate_mono (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true)
        (k : ℕ) (hk : gateVal n C k x = true) : gateVal n C k y = true := by
      have hwle : wLe (List.ofFn x) (List.ofFn y) := by
        refine ⟨by simp only [List.length_ofFn], ?_⟩
        intro i hi
        by_cases hin : i < n
        · have h1 : (List.ofFn x).getD i false = x ⟨i, hin⟩ := by
            rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hin), List.getElem_ofFn]
          have h2 : (List.ofFn y).getD i false = y ⟨i, hin⟩ := by
            rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hin), List.getElem_ofFn]
          rw [h1] at hi
          rw [h2]
          exact hxy ⟨i, hin⟩ hi
        · rw [List.getD_eq_default (List.ofFn x) false (n := i) (by rw [List.length_ofFn]; omega)] at hi
          cases hi
      exact (run_mono C.gates hmono (List.ofFn x) (List.ofFn y) hwle).2 (n + k) hk
    have hgateVal_step (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
        let g := C.gates[k]'hk
        gateVal n C k x = g.op.eval (g.inputs.map fun i => (run (C.gates.take k) (List.ofFn x)).getD i false) := by
      dsimp only
      have hsplit : C.gates = C.gates.take k ++ (C.gates[k]'hk :: C.gates.drop (k + 1)) := by
        have h1 : C.gates.take k ++ C.gates.drop k = C.gates := List.take_append_drop k C.gates
        have h2 : C.gates.drop k = C.gates[k]'hk :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk
        rw [← h2]; exact h1.symm
      have hlen_pre : (run (C.gates.take k) (List.ofFn x)).length = n + k := by
        rw [run_len, List.length_ofFn, List.length_take]; omega
      change (run C.gates (List.ofFn x)).getD (n + k) false = _
      conv_lhs => rw [hsplit, run_append]
      change (run (C.gates.drop (k + 1)) (step (run (C.gates.take k) (List.ofFn x)) (C.gates[k]'hk))).getD (n + k) false = _
      rw [run_keep (C.gates.drop (k + 1)) _ (n + k) (by simp only [step, List.length_append, hlen_pre, List.length_cons, List.length_nil]; omega)]
      dsimp only [step]
      simpa only [hlen_pre] using getD_snoc_eq (run (C.gates.take k) (List.ofFn x))
        ((C.gates[k]'hk).op.eval ((C.gates[k]'hk).inputs.map fun i => (run (C.gates.take k) (List.ofFn x)).getD i false)) false
    have hEveryOwned : EveryEdgeOwned n G C := by
      intro u v huv
      have hex_and : ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ gateVal n C j (pairInput u v) = true := by
        by_contra hno
        have hno_and : ∀ (k : ℕ) (hk : k < C.gates.length), (C.gates[k]'hk).op = GateOp.and →
            gateVal n C k (pairInput u v) = false := by
          intro k hk hop
          cases hgv : gateVal n C k (pairInput u v) with
          | false => rfl
          | true =>
            have hga : gateAt C k = C.gates[k]'hk := by
              change C.gates.getD k (Gate.mk GateOp.or []) = _
              exact List.getD_eq_getElem _ _ hk
            exact False.elim (hno ⟨k, hk, by rw [hga]; exact hop, hgv⟩)
        have hor_dist (wUV wUU wVV : List Bool) (heq : ∀ i, wUV.getD i false = (wUU.getD i false || wVV.getD i false))
            (l : List ℕ) :
            (l.map fun i => wUV.getD i false).any id =
              ((l.map fun i => wUU.getD i false).any id || (l.map fun i => wVV.getD i false).any id) := by
          induction l with
          | nil => rfl
          | cons a t ih =>
            simp only [List.map_cons, List.any_cons, id_eq]
            rw [heq a, ih]
            ac_rfl
        have hsplit_wires : ∀ k ≤ C.gates.length, ∀ i : ℕ,
            (run (C.gates.take k) (List.ofFn (pairInput u v))).getD i false =
              ((run (C.gates.take k) (List.ofFn (pairInput u u))).getD i false ||
               (run (C.gates.take k) (List.ofFn (pairInput v v))).getD i false) := by
          intro k
          induction k with
          | zero =>
            intro _ i
            dsimp only [List.take_zero, run, List.foldl_nil]
            by_cases hin : i < n
            · rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hin), List.getElem_ofFn,
                  List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hin), List.getElem_ofFn,
                  List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hin), List.getElem_ofFn]
              change decide (⟨i, hin⟩ = u ∨ ⟨i, hin⟩ = v) =
                (decide (⟨i, hin⟩ = u ∨ ⟨i, hin⟩ = u) || decide (⟨i, hin⟩ = v ∨ ⟨i, hin⟩ = v))
              by_cases hu : (⟨i, hin⟩ : Fin n) = u <;> by_cases hv : (⟨i, hin⟩ : Fin n) = v <;>
                simp only [hu, hv, true_or, or_true, or_false, decide_true, decide_false, Bool.or_false, Bool.true_or, Bool.or_true]
            · rw [List.getD_eq_default (List.ofFn _) false (n := i) (by rw [List.length_ofFn]; omega),
                  List.getD_eq_default (List.ofFn _) false (n := i) (by rw [List.length_ofFn]; omega),
                  List.getD_eq_default (List.ofFn _) false (n := i) (by rw [List.length_ofFn]; omega)]
              rfl
          | succ k ih =>
            intro hk i
            have hk_lt : k < C.gates.length := by omega
            have htake : C.gates.take (k + 1) = C.gates.take k ++ [C.gates[k]'hk_lt] :=
              List.take_succ_eq_append_getElem hk_lt
            let g := C.gates[k]'hk_lt
            let wUV := run (C.gates.take k) (List.ofFn (pairInput u v))
            let wUU := run (C.gates.take k) (List.ofFn (pairInput u u))
            let wVV := run (C.gates.take k) (List.ofFn (pairInput v v))
            have hlenUV : wUV.length = n + k := by dsimp only [wUV]; rw [run_len, List.length_ofFn, List.length_take]; omega
            have hlenUU : wUU.length = n + k := by dsimp only [wUU]; rw [run_len, List.length_ofFn, List.length_take]; omega
            have hlenVV : wVV.length = n + k := by dsimp only [wVV]; rw [run_len, List.length_ofFn, List.length_take]; omega
            have hih := ih (by omega)
            have hbit_eq : g.op.eval (g.inputs.map fun j => wUV.getD j false) =
                (g.op.eval (g.inputs.map fun j => wUU.getD j false) ||
                 g.op.eval (g.inputs.map fun j => wVV.getD j false)) := by
              rcases (hmono g (List.getElem_mem hk_lt)).1 with hop | hop
              · have hgv_uv : gateVal n C k (pairInput u v) = false := hno_and k hk_lt hop
                have hgv_uu : gateVal n C k (pairInput u u) = false := by
                  cases h : gateVal n C k (pairInput u u) with
                  | false => rfl
                  | true =>
                    have hle : ∀ z : Fin n, pairInput u u z = true → pairInput u v z = true := by
                      intro z hz
                      change decide (z = u ∨ z = u) = true at hz
                      change decide (z = u ∨ z = v) = true
                      simp only [decide_eq_true_eq, or_self] at hz ⊢
                      exact Or.inl hz
                    have h1 := hgate_mono (pairInput u u) (pairInput u v) hle k h
                    rw [hgv_uv] at h1; cases h1
                have hgv_vv : gateVal n C k (pairInput v v) = false := by
                  cases h : gateVal n C k (pairInput v v) with
                  | false => rfl
                  | true =>
                    have hle : ∀ z : Fin n, pairInput v v z = true → pairInput u v z = true := by
                      intro z hz
                      change decide (z = v ∨ z = v) = true at hz
                      change decide (z = u ∨ z = v) = true
                      simp only [decide_eq_true_eq, or_self] at hz ⊢
                      exact Or.inr hz
                    have h1 := hgate_mono (pairInput v v) (pairInput u v) hle k h
                    rw [hgv_uv] at h1; cases h1
                rw [← hgateVal_step (pairInput u v) k hk_lt, ← hgateVal_step (pairInput u u) k hk_lt,
                    ← hgateVal_step (pairInput v v) k hk_lt, hgv_uv, hgv_uu, hgv_vv]
                rfl
              · rw [hop]
                exact hor_dist wUV wUU wVV hih g.inputs
            rw [htake, run_append, run_append, run_append]
            change (wUV ++ [g.op.eval (g.inputs.map fun j => wUV.getD j false)]).getD i false =
              ((wUU ++ [g.op.eval (g.inputs.map fun j => wUU.getD j false)]).getD i false ||
               (wVV ++ [g.op.eval (g.inputs.map fun j => wVV.getD j false)]).getD i false)
            by_cases hieq : i = n + k
            · subst hieq
              rw [← hlenUV, getD_snoc_eq wUV _ false, show wUV.length = wUU.length by omega, getD_snoc_eq wUU _ false,
                  show wUU.length = wVV.length by omega, getD_snoc_eq wVV _ false]
              exact hbit_eq
            · rw [getD_snoc_ne wUV _ false i (by omega), getD_snoc_ne wUU _ false i (by omega),
                  getD_snoc_ne wVV _ false i (by omega)]
              exact hih i
        have hfin := hsplit_wires C.gates.length (Nat.le_refl _) C.output
        rw [List.take_length] at hfin
        have hev_uv : circuitFun n C (pairInput u v) = true := by
          rw [hfun]
          change (decide (∃ a ∈ (∅ : Finset (Fin n)), pairInput u v a = true) ||
            decide (∃ a b : Fin n, G.Adj a b ∧ pairInput u v a = true ∧ pairInput u v b = true)) = true
          have hr : decide (∃ a b : Fin n, G.Adj a b ∧ pairInput u v a = true ∧ pairInput u v b = true) = true := by
            rw [decide_eq_true_eq]
            exact ⟨u, v, huv, by change decide (u = u ∨ u = v) = true; simp only [true_or, decide_true],
              by change decide (v = u ∨ v = v) = true; simp only [or_true, decide_true]⟩
          rw [hr, Bool.or_true]
        have hev_self (a : Fin n) : circuitFun n C (pairInput a a) = false := by
          rw [hfun]
          change (decide (∃ z ∈ (∅ : Finset (Fin n)), pairInput a a z = true) ||
            decide (∃ x y : Fin n, G.Adj x y ∧ pairInput a a x = true ∧ pairInput a a y = true)) = false
          have hl : decide (∃ z ∈ (∅ : Finset (Fin n)), pairInput a a z = true) = false := by
            rw [decide_eq_false_iff_not]
            intro h; obtain ⟨z, hz, _⟩ := h; exact Finset.notMem_empty z hz
          have hr : decide (∃ x y : Fin n, G.Adj x y ∧ pairInput a a x = true ∧ pairInput a a y = true) = false := by
            rw [decide_eq_false_iff_not]
            intro h
            obtain ⟨x, y, hxy, hx, hy⟩ := h
            change decide (x = a ∨ x = a) = true at hx
            change decide (y = a ∨ y = a) = true at hy
            simp only [decide_eq_true_eq, or_self] at hx hy
            subst hx; subst hy
            exact G.ne_of_adj hxy rfl
          rw [hl, hr]; rfl
        have h1 : circuitFun n C (pairInput u v) = (circuitFun n C (pairInput u u) || circuitFun n C (pairInput v v)) := hfin
        rw [hev_uv, hev_self u, hev_self v] at h1
        cases h1
      have hleast : ∀ bound : ℕ, (∃ j < bound, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧ gateVal n C j (pairInput u v) = true) →
          ∃ j < C.gates.length, Owns n C j u v := by
        intro bound
        induction bound with
        | zero => intro h; obtain ⟨j, hj, _⟩ := h; omega
        | succ b ih =>
          intro h
          by_cases hlt : ∃ j < b, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧ gateVal n C j (pairInput u v) = true
          · exact ih hlt
          · obtain ⟨j, hjb, hjlen, hjop, hjv⟩ := h
            have hjeq : j = b := by by_contra hne; exact hlt ⟨j, by omega, hjlen, hjop, hjv⟩
            refine ⟨j, hjlen, hjlen, hjop, hjv, ?_⟩
            intro i hij _ hiop
            cases hiv : gateVal n C i (pairInput u v) with
            | false => rfl
            | true => exact False.elim (hlt ⟨i, by omega, by omega, hiop, hiv⟩)
      obtain ⟨j, hjlen, hjop, hjv⟩ := hex_and
      exact hleast C.gates.length ⟨j, hjlen, hjlen, hjop, hjv⟩
    let U_unit : Finset (Sym2 (Fin n)) :=
      U.filter fun e => ∃ u v : Fin n, e = s(u, v) ∧ ∃ j : Fin C.gates.length, Owns n C j.val u v ∧
        ∃ a : Fin n, gateVal n C j.val (pairInput a a) = true
    let U_nonedge : Finset (Sym2 (Fin n)) :=
      U.filter fun e => ∀ u v : Fin n, e = s(u, v) → ∀ j : Fin C.gates.length, Owns n C j.val u v →
        (∀ a : Fin n, gateVal n C j.val (pairInput a a) = false) ∧
        ∃ a b : Fin n, a ≠ b ∧ ¬ G.Adj a b ∧ gateVal n C j.val (pairInput a b) = true
    have hU_cover : U ⊆ U_unit ∪ U_nonedge := by
      intro e he
      rw [Finset.mem_union]
      by_cases hunit : ∃ u v : Fin n, e = s(u, v) ∧ ∃ j : Fin C.gates.length, Owns n C j.val u v ∧
          ∃ a : Fin n, gateVal n C j.val (pairInput a a) = true
      · exact Or.inl (Finset.mem_filter.mpr ⟨he, hunit⟩)
      · refine Or.inr (Finset.mem_filter.mpr ⟨he, ?_⟩)
        intro u v heuv j howns
        have hno_unit : ∀ a : Fin n, gateVal n C j.val (pairInput a a) = false := by
          intro a
          cases hga : gateVal n C j.val (pairInput a a) with
          | false => rfl
          | true => exact False.elim (hunit ⟨u, v, heuv, j, howns, a, hga⟩)
        refine ⟨hno_unit, ?_⟩
        have hmem_clean := hUsub he
        rw [Finset.mem_filter] at hmem_clean
        have hnot_clean : ¬ ∀ a b : Fin n, gateVal n C j.val (pairInput a b) = true → G.Adj a b :=
          fun hall => hmem_clean.2 ⟨u, v, heuv, j, howns, hall⟩
        have hex_ne : ∃ a b : Fin n, gateVal n C j.val (pairInput a b) = true ∧ ¬ G.Adj a b := by
          by_contra hno
          exact hnot_clean (fun a b hgt => by
            by_contra hnadj
            exact hno ⟨a, b, hgt, hnadj⟩)
        obtain ⟨a, b, hgt, hnadj⟩ := hex_ne
        have hab : a ≠ b := by
          intro heq; subst heq
          rw [hno_unit a] at hgt
          cases hgt
        exact ⟨a, b, hab, hnadj, hgt⟩
    have hcard_sum : U.card ≤ U_unit.card + U_nonedge.card :=
      le_trans (Finset.card_le_card hU_cover) (Finset.card_union_le U_unit U_nonedge)
    have hd1 : d1 ≤ max d1 (max d2 d3) := le_max_left _ _
    have hd2 : d2 ≤ max d1 (max d2 d3) := le_trans (le_max_left _ _) (le_max_right _ _)
    have hd3 : d3 ≤ max d1 (max d2 d3) := le_trans (le_max_right _ _) (le_max_right _ _)
    have hdeg_le (d' : ℕ) (hd' : d' ≤ max d1 (max d2 d3)) :
        ∀ v : Fin n, {e ∈ U | v ∈ e}.card = 0 ∨ d' < {e ∈ U | v ∈ e}.card := by
      intro v
      rcases hUdeg v with h0 | hgt
      · exact Or.inl h0
      · exact Or.inr (by omega)
    by_cases hhalf : U.card ≤ 2 * U_unit.card
    · have h1 := hc1 n G hdeg hgirth C hmono hfun hEveryOwned U hUsub hUne (hdeg_le d1 hd1)
        U_unit (Finset.filter_subset _ U) hhalf (fun e he => (Finset.mem_filter.mp he).2)
      have hc1_le : c1 ≤ max c1 (max c2 c3) := le_max_left _ _
      exact le_trans h1 (Nat.mul_le_mul_right (C.size + 1) hc1_le)
    · have hhalf2 : U.card ≤ 2 * U_nonedge.card := by omega
      by_cases hstar : HasStarProfile n G C
      · have h2 := hc2 n G hdeg hgirth C hmono hfun hEveryOwned hstar U hUsub hUne (hdeg_le d2 hd2)
          U_nonedge (Finset.filter_subset _ U) hhalf2 (fun e he => (Finset.mem_filter.mp he).2)
        have hc2_le : c2 ≤ max c1 (max c2 c3) := le_trans (le_max_left _ _) (le_max_right _ _)
        exact le_trans h2 (Nat.mul_le_mul_right (C.size + 1) hc2_le)
      · have h3 := hc3 n G hdeg hgirth C hmono hfun hEveryOwned hstar U hUsub hUne (hdeg_le d3 hd3)
          U_nonedge (Finset.filter_subset _ U) hhalf2 (fun e he => (Finset.mem_filter.mp he).2)
        have hc3_le : c3 ≤ max c1 (max c2 c3) := le_trans (le_max_right _ _) (le_max_right _ _)
        exact le_trans h3 (Nat.mul_le_mul_right (C.size + 1) hc3_le)
  · have hU0 : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hUne
    rw [hU0, Finset.card_empty]
    exact Nat.zero_le _
