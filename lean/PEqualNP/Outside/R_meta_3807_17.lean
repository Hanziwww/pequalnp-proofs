import Mathlib.Combinatorics.SimpleGraph.Paths
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_3807_17
    (hUnit : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      G.edgeFinset.Nonempty →
      ∀ (C : Circuit), IsLeastAO G C → TopForm G C → 3 ≤ (junk G C).card →
        (∀ j1 ∈ junk G C, ∀ j2 ∈ junk G C, ¬ InCone n C j1 j2) →
        ∀ T : Finset (Sym2 (Fin n)),
          (∀ e ∈ T, e ∈ Ustar G C ∧ ∃ (u v : Fin n), e = s(u, v) ∧
            ∃ t ∈ tops G C, ∃ j1 ∈ junk G C, ∃ j2 ∈ junk G C, j1 ≠ j2 ∧
              ∃ b : Fin 2, OrReaches n C (opnd C t b) j1 ∧ OrReaches n C (opnd C t (1 - b)) j2 ∧
                u ∈ side C j1 0 ∧ u ∈ side C j1 1 ∧
                (u ∈ side C j2 0 ∨ v ∈ side C j2 0) ∧
                (u ∈ side C j2 1 ∨ v ∈ side C j2 1)) →
          T.card ≤ c * (C.size + 1))
    (hStar : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      G.edgeFinset.Nonempty →
      ∀ (C : Circuit), IsLeastAO G C → TopForm G C → 3 ≤ (junk G C).card →
        (∀ j1 ∈ junk G C, ∀ j2 ∈ junk G C, ¬ InCone n C j1 j2) →
        ∀ T : Finset (Sym2 (Fin n)),
          (∀ e ∈ T, e ∈ Ustar G C ∧ ∃ (u v : Fin n), e = s(u, v) ∧
            ∃ t ∈ tops G C, ∃ j1 ∈ junk G C, ∃ j2 ∈ junk G C, j1 ≠ j2 ∧
              OrReaches n C (opnd C t 0) j1 ∧ OrReaches n C (opnd C t 1) j2 ∧
              ∃ b1 b2 : Fin 2, u ∈ side C j1 b1 ∧ u ∈ side C j2 b2 ∧
                v ∈ side C j1 (1 - b1) ∧ v ∈ side C j2 (1 - b2) ∧
                ∀ (w : Fin n), w ∈ side C j1 b1 → w ∈ side C j2 b2 → w = u) →
          T.card ≤ c * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (3 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (∀ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∀ x13 ∈ PEqualNP.TopForm.junk x3 x7, ¬PEqualNP.EdgeOwnership.InCone x2 x7 x11 x13) → {x12 ∈ PEqualNP.TopForm.Ustar x3 x7 | ∃ (x13 : Fin x2) (x14 : Fin x2), x12 = s(x13, x14) ∧ ∃ x15 ∈ PEqualNP.TopForm.tops x3 x7, ∃ x16 ∈ PEqualNP.TopForm.junk x3 x7, ∃ x17 ∈ PEqualNP.TopForm.junk x3 x7, x16 ≠ x17 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x7 (PEqualNP.TopForm.opnd x7 x15 (0 : Fin (2 : ℕ))) x16 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x7 (PEqualNP.TopForm.opnd x7 x15 (1 : Fin (2 : ℕ))) x17 ∧ PEqualNP.EdgeOwnership.gateVal x2 x7 x16 (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x2 x7 x17 (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.true}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨c1, hc1⟩ := hUnit
  obtain ⟨c2, hc2⟩ := hStar
  refine ⟨c1 + c2, ?_⟩
  intro n G _ hgirth hne C hleast htop hjunk3 hno_jcone
  have hAO2 : IsAO2 n C := hleast.1
  have hAndOr : AndOrOnly C := hAO2.1
  have hReads : ReadsBack n C := hAO2.2.1
  have hLen2 : ∀ g ∈ C.gates, g.inputs.length = 2 := hAO2.2.2
  have hgetD_snoc {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  have snoc_foldl {α : Type} (F : List α → Gate → α) (d : α) :
      ∀ (gs : List Gate) (acc : List α),
        (gs.foldl (fun s g => s ++ [F s g]) acc).length = acc.length + gs.length ∧
        ∀ i < acc.length, (gs.foldl (fun s g => s ++ [F s g]) acc).getD i d = acc.getD i d := by
    intro gs
    induction gs with
    | nil =>
      intro acc
      exact ⟨by simp only [List.foldl_nil, List.length_nil, Nat.add_zero], fun _ _ => rfl⟩
    | cons g gs ih =>
      intro acc
      have h := ih (acc ++ [F acc g])
      refine ⟨?_, ?_⟩
      · simp only [List.foldl_cons, h.1, List.length_append, List.length_cons, List.length_nil]
        omega
      · intro i hi
        simp only [List.foldl_cons]
        rw [h.2 i (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)]
        exact List.getD_append _ _ _ _ hi
  have split_at (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
      gs = gs.take j ++ gs.getD j ⟨GateOp.or, []⟩ :: gs.drop (j + 1) := by
    have h1 := (List.take_append_drop j gs).symm
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [List.getD_eq_getElem gs ⟨GateOp.or, []⟩ hj, ← h2]
    exact h1
  have snoc_foldl_eq {α : Type} (F : List α → Gate → α) (d : α) (init : List α)
      (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
      let acc := (gs.take j).foldl (fun s g => s ++ [F s g]) init
      acc.length = init.length + j ∧
      (∀ i < init.length + j, acc.getD i d = (gs.foldl (fun s g => s ++ [F s g]) init).getD i d) ∧
      (gs.foldl (fun s g => s ++ [F s g]) init).getD (init.length + j) d =
        F acc (gs.getD j ⟨GateOp.or, []⟩) := by
    intro acc
    have htake_len : (gs.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
    have hacc_len : acc.length = init.length + j := by
      have h := (snoc_foldl F d (gs.take j) init).1
      rw [htake_len] at h
      exact h
    have hgs := split_at gs j hj
    have hfold : gs.foldl (fun s g => s ++ [F s g]) init =
        (gs.drop (j + 1)).foldl (fun s g => s ++ [F s g]) (acc ++ [F acc (gs.getD j ⟨GateOp.or, []⟩)]) := by
      conv_lhs => rw [hgs]
      rw [List.foldl_append, List.foldl_cons]
    refine ⟨hacc_len, ?_, ?_⟩
    · intro i hi
      rw [hfold]
      rw [(snoc_foldl F d (gs.drop (j + 1)) (acc ++ [F acc (gs.getD j ⟨GateOp.or, []⟩)])).2 i
        (by simp only [List.length_append, List.length_cons, List.length_nil, hacc_len]; omega)]
      exact (List.getD_append _ _ _ _ (by omega)).symm
    · rw [hfold]
      rw [(snoc_foldl F d (gs.drop (j + 1)) (acc ++ [F acc (gs.getD j ⟨GateOp.or, []⟩)])).2 (init.length + j)
        (by simp only [List.length_append, List.length_cons, List.length_nil, hacc_len]; omega)]
      rw [← hacc_len]
      exact hgetD_snoc acc (F acc (gs.getD j ⟨GateOp.or, []⟩)) d
  have hgate_mem (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    dsimp only [gateAt]
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have hgate_op (j : ℕ) (hj : j < C.gates.length) :
      (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or :=
    hAndOr (gateAt C j) (hgate_mem j hj)
  have hgate_ins (j : ℕ) (hj : j < C.gates.length) :
      (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
    have hl : (gateAt C j).inputs.length = 2 := hLen2 (gateAt C j) (hgate_mem j hj)
    rcases hi : (gateAt C j).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp only [hi, List.length_nil] at hl; omega
    · simp only [hi, List.length_cons, List.length_nil] at hl; omega
    · change [a, b] = [(gateAt C j).inputs.getD 0 0, (gateAt C j).inputs.getD 1 0]
      rw [hi]
      rfl
    · simp only [hi, List.length_cons] at hl; omega
  have hopnd_lt (j : ℕ) (hj : j < C.gates.length) (b : Fin 2) : opnd C j b < n + j := by
    apply hReads j hj
    rw [hgate_ins j hj]
    fin_cases b
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
  have hwire_in (x : Fin n → Bool) (i : Fin n) : wireVal n C i.val x = x i := by
    dsimp only [wireVal, Circuit.wires]
    have hkeep := (snoc_foldl (fun w g => g.op.eval (g.inputs.map fun k => w.getD k false))
      false C.gates (List.ofFn x)).2 i.val (by simp only [List.length_ofFn]; exact i.isLt)
    rw [hkeep, List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact i.isLt),
      List.getElem_ofFn]
  have hwire_gate (j : ℕ) (hj : j < C.gates.length) (x : Fin n → Bool) :
      gateVal n C j x =
        (gateAt C j).op.eval [wireVal n C (opnd C j 0) x, wireVal n C (opnd C j 1) x] := by
    let F : List Bool → Gate → Bool :=
      fun w g => g.op.eval (g.inputs.map fun k => w.getD k false)
    have hspec := snoc_foldl_eq F false (List.ofFn x) C.gates j hj
    have hlen_ofFn : (List.ofFn x).length = n := List.length_ofFn
    have h1 := hspec.2.2
    rw [hlen_ofFn] at h1
    change gateVal n C j x = F _ (gateAt C j) at h1
    rw [h1]
    dsimp only [F]
    rw [hgate_ins j hj]
    simp only [List.map_cons, List.map_nil]
    have h0 := hspec.2.1 (opnd C j 0) (by rw [hlen_ofFn]; exact hopnd_lt j hj 0)
    have h2 := hspec.2.1 (opnd C j 1) (by rw [hlen_ofFn]; exact hopnd_lt j hj 1)
    rw [h0, h2]
    rfl
  have hgate_and_eval (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
      (x : Fin n → Bool) :
      gateVal n C j x = (wireVal n C (opnd C j 0) x && wireVal n C (opnd C j 1) x) := by
    rw [hwire_gate j hj x, hop]
    change (wireVal n C (opnd C j 0) x && (wireVal n C (opnd C j 1) x && true)) = _
    rw [Bool.and_true]
  have hgate_or_eval (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
      (x : Fin n → Bool) :
      gateVal n C j x = (wireVal n C (opnd C j 0) x || wireVal n C (opnd C j 1) x) := by
    rw [hwire_gate j hj x, hop]
    change (wireVal n C (opnd C j 0) x || (wireVal n C (opnd C j 1) x || false)) = _
    rw [Bool.or_false]
  have hinCone_iff (i j : ℕ) (hj : j < C.gates.length) :
      InCone n C i j ↔
        ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
    let F : List (List ℕ) → Gate → List ℕ :=
      fun cs g => (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) [])
    have hspec := snoc_foldl_eq F [] [] C.gates j hj
    have hlen_nil : ([] : List (List ℕ)).length = 0 := rfl
    have h0 := hspec.1
    have h1 := hspec.2.1
    have h2 := hspec.2.2
    rw [hlen_nil, Nat.zero_add] at h0 h1 h2
    have hcones_eq : cones n C = C.gates.foldl (fun s g => s ++ [F s g]) [] := rfl
    change i ∈ (cones n C).getD j [] ↔ _
    rw [hcones_eq, h2]
    dsimp only [F]
    rw [h0, List.mem_flatMap]
    constructor
    · intro h
      obtain ⟨w, hw, hi⟩ := h
      rw [List.mem_filter, decide_eq_true_iff] at hw
      have hsub : w - n < j := by omega
      have hacc := h1 (w - n) hsub
      rw [hacc] at hi
      rcases List.mem_cons.mp hi with rfl | htail
      · exact ⟨w, hw.1, hw.2.1, hw.2.2, Or.inl rfl⟩
      · exact ⟨w, hw.1, hw.2.1, hw.2.2, Or.inr htail⟩
    · intro h
      obtain ⟨w, hwin, hnw, hwlt, hchoice⟩ := h
      refine ⟨w, ?_, ?_⟩
      · rw [List.mem_filter, decide_eq_true_iff]
        exact ⟨hwin, hnw, hwlt⟩
      · have hsub : w - n < j := by omega
        rw [h1 (w - n) hsub]
        rcases hchoice with rfl | htail
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ htail
  have hinCone_lt : ∀ j : ℕ, ∀ i : ℕ, InCone n C i j → i < j ∧ j < C.gates.length := by
    intro j
    induction j using Nat.strongRecOn with
    | ind j ih =>
      intro i hij
      by_cases hj : j < C.gates.length
      · rw [hinCone_iff i j hj] at hij
        obtain ⟨w, _, hnw, hwlt, hchoice⟩ := hij
        rcases hchoice with rfl | htail
        · exact ⟨by omega, hj⟩
        · have hprev := ih (w - n) (by omega) i htail
          exact ⟨by omega, hj⟩
      · exfalso
        have hlen : (cones n C).length = C.gates.length := by
          let F : List (List ℕ) → Gate → List ℕ :=
            fun cs g => (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
              (fun w => (w - n) :: cs.getD (w - n) [])
          have h := (snoc_foldl F [] C.gates []).1
          change (C.gates.foldl (fun s g => s ++ [F s g]) []).length = C.gates.length
          simpa only [List.length_nil, Nat.zero_add] using h
        have hemp : (cones n C).getD j [] = [] := List.getD_eq_default _ _ (by omega)
        change i ∈ (cones n C).getD j [] at hij
        rw [hemp] at hij
        cases hij
  have hinCone_trans : ∀ c : ℕ, ∀ a b : ℕ, InCone n C a b → InCone n C b c → InCone n C a c := by
    intro c
    induction c using Nat.strongRecOn with
    | ind c ih =>
      intro a b hab hbc
      have hc : c < C.gates.length := (hinCone_lt c b hbc).2
      rw [hinCone_iff b c hc] at hbc
      obtain ⟨w, hwin, hnw, hwlt, hchoice⟩ := hbc
      rw [hinCone_iff a c hc]
      refine ⟨w, hwin, hnw, hwlt, Or.inr ?_⟩
      rcases hchoice with rfl | htail
      · exact hab
      · exact ih (w - n) (by omega) a b hab htail
  have hite_t {α : Type} {c : Prop} (d : Decidable c) (hc : c) (a b : α) :
      @ite α c d a b = a := by
    cases d with
    | isTrue _ => rfl
    | isFalse hn => exact (hn hc).elim
  have hite_f {α : Type} {c : Prop} (d : Decidable c) (hc : ¬ c) (a b : α) :
      @ite α c d a b = b := by
    cases d with
    | isTrue hp => exact (hc hp).elim
    | isFalse _ => rfl
  have mem_fil {α : Type} {p : α → Prop} {inst : DecidablePred p} {s : Finset α} {x : α} :
      x ∈ @Finset.filter α p inst s ↔ x ∈ s ∧ p x := Finset.mem_filter
  have horReaches_iff (k g : ℕ) (hk : k < C.gates.length) :
      OrReaches n C (n + k) g ↔
        g = k ∨ ((gateAt C k).op = GateOp.or ∧
          ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ OrReaches n C w g) := by
    let F : List (List ℕ) → Gate → List ℕ :=
      fun cs g => cs.length :: (@ite _ (g.op = GateOp.or) (gateOpDecEq g.op GateOp.or)
        ((g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
          (fun w => cs.getD (w - n) []))
        [])
    have hspec := snoc_foldl_eq F [] [] C.gates k hk
    have hlen_nil : ([] : List (List ℕ)).length = 0 := rfl
    have h0 := hspec.1
    have h1 := hspec.2.1
    have h2 := hspec.2.2
    rw [hlen_nil, Nat.zero_add] at h0 h1 h2
    have horSets_eq : orSets n C = C.gates.foldl (fun s g => s ++ [F s g]) [] := rfl
    change (n ≤ n + k ∧ g ∈ (orSets n C).getD (n + k - n) []) ↔ _
    rw [Nat.add_sub_cancel_left, horSets_eq, h2]
    dsimp only [F]
    rw [h0]
    constructor
    · intro h
      rcases List.mem_cons.mp h.2 with rfl | htail
      · exact Or.inl rfl
      · by_cases hop : (gateAt C k).op = GateOp.or
        · have hop' : (C.gates.getD k ⟨GateOp.or, []⟩).op = GateOp.or := hop
          rw [hite_t (gateOpDecEq _ _) hop', List.mem_flatMap] at htail
          obtain ⟨w, hw, hg⟩ := htail
          rw [List.mem_filter, decide_eq_true_iff] at hw
          have hsub : w - n < k := by omega
          rw [h1 (w - n) hsub] at hg
          exact Or.inr ⟨hop, w, hw.1, hw.2.1, hw.2.2, hw.2.1, hg⟩
        · have hop' : ¬ (C.gates.getD k ⟨GateOp.or, []⟩).op = GateOp.or := hop
          rw [hite_f (gateOpDecEq _ _) hop'] at htail
          cases htail
    · intro h
      refine ⟨Nat.le_add_right n k, ?_⟩
      rcases h with rfl | ⟨hop, w, hwin, hnw, hwlt, hreach⟩
      · exact List.mem_cons_self
      · refine List.mem_cons_of_mem k ?_
        have hop' : (C.gates.getD k ⟨GateOp.or, []⟩).op = GateOp.or := hop
        rw [hite_t (gateOpDecEq _ _) hop', List.mem_flatMap]
        refine ⟨w, ?_, ?_⟩
        · rw [List.mem_filter, decide_eq_true_iff]
          exact ⟨hwin, hnw, hwlt⟩
        · have hsub : w - n < k := by omega
          rw [h1 (w - n) hsub]
          exact hreach.2
  have horReaches_lt (w g : ℕ) (h : OrReaches n C w g) : w < n + C.gates.length := by
    by_contra hge
    have hlen : (orSets n C).length = C.gates.length := by
      let F : List (List ℕ) → Gate → List ℕ :=
        fun cs g => cs.length :: (@ite _ (g.op = GateOp.or) (gateOpDecEq g.op GateOp.or)
          ((g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
            (fun w => cs.getD (w - n) []))
          [])
      have h0 := (snoc_foldl F [] C.gates []).1
      change (C.gates.foldl (fun s g => s ++ [F s g]) []).length = C.gates.length
      simpa only [List.length_nil, Nat.zero_add] using h0
    have hemp : (orSets n C).getD (w - n) [] = [] :=
      List.getD_eq_default _ _ (by have := h.1; omega)
    have hm := h.2
    rw [hemp] at hm
    cases hm
  have horReaches_true : ∀ k : ℕ, ∀ g : ℕ, ∀ x : Fin n → Bool,
      OrReaches n C (n + k) g → gateVal n C g x = true → wireVal n C (n + k) x = true := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro g x hr hg
      have hk : k < C.gates.length := by
        have := horReaches_lt (n + k) g hr
        omega
      rw [horReaches_iff k g hk] at hr
      rcases hr with rfl | ⟨hop, w, hwin, hnw, hwlt, hwr⟩
      · exact hg
      · have hprev : wireVal n C w x = true := by
          have hw_eq : w = n + (w - n) := by omega
          rw [hw_eq] at hwr ⊢
          exact ih (w - n) (by omega) g x hwr hg
        have heval : gateVal n C k x = (wireVal n C (opnd C k 0) x || wireVal n C (opnd C k 1) x) :=
          hgate_or_eval k hk hop x
        change gateVal n C k x = true
        rw [heval]
        rw [hgate_ins k hk] at hwin
        rcases List.mem_cons.mp hwin with rfl | hwin'
        · rw [hprev]; rfl
        · rw [List.mem_singleton] at hwin'
          rw [← hwin', hprev, Bool.or_true]
  have hjunk_cone_or (j i : ℕ) (hj : j ∈ junk G C) (hi : InCone n C i j) :
      (gateAt C i).op = GateOp.or := by
    have hj_lt : j < C.gates.length := (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
    have hj_and : (gateAt C j).op = GateOp.and := (Finset.mem_filter.mp hj).2.1
    have hi_lt : i < C.gates.length := by
      have := hinCone_lt j i hi
      omega
    rcases hgate_op i hi_lt with hand | hor
    · exfalso
      by_cases hbf : BelowF G C i
      · exact htop i hi_lt j hj_lt hand hbf hj_and hi
      · have hi_junk : i ∈ junk G C := by
          change i ∈ (Finset.range C.gates.length).filter (fun k => IsDirtyAnd n G C k)
          rw [Finset.mem_filter, Finset.mem_range]
          refine ⟨hi_lt, hand, hi_lt, ?_⟩
          by_contra hno
          apply hbf
          intro x hxt
          cases hgx : graphFun G ∅ x with
          | true => rfl
          | false => exact (hno ⟨x, hxt, hgx⟩).elim
        exact hno_jcone i hi_junk j hj hi
    · exact hor
  have horIn_mem_def (w : ℕ) (a : Fin n) :
      a ∈ orIn n C w ↔ (a : ℕ) = w ∨ ∃ k < C.gates.length,
        OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧ (a : ℕ) ∈ (gateAt C k).inputs := by
    unfold orIn
    exact mem_fil.trans (and_iff_right (Finset.mem_univ a))
  have horIn_iff : ∀ w : ℕ, ∀ j ∈ junk G C,
      (w < n ∨ (n ≤ w ∧ InCone n C (w - n) j)) →
      ∀ x : Fin n → Bool, wireVal n C w x = true ↔ ∃ a ∈ orIn n C w, x a = true := by
    intro w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro j hj hcond x
      rcases hcond with hw_in | ⟨hnw, hcone⟩
      · let a0 : Fin n := ⟨w, hw_in⟩
        have hval : wireVal n C w x = x a0 := hwire_in x a0
        rw [hval]
        constructor
        · intro hx
          refine ⟨a0, ?_, hx⟩
          rw [horIn_mem_def]
          exact Or.inl rfl
        · intro hx
          obtain ⟨a, ha, hxa⟩ := hx
          rw [horIn_mem_def] at ha
          rcases ha with heq | ⟨k, _, hreach, _, _⟩
          · have ha_eq : a = a0 := Fin.ext heq
            rwa [← ha_eq]
          · exfalso
            have := hreach.1
            omega
      · let k := w - n
        have hw_eq : w = n + k := by omega
        have hk_lt : k < C.gates.length := by
          have := hinCone_lt j k hcone
          omega
        have hk_or : (gateAt C k).op = GateOp.or := hjunk_cone_or j k hj hcone
        have h0_lt : opnd C k 0 < w := by
          have := hopnd_lt k hk_lt 0
          omega
        have h1_lt : opnd C k 1 < w := by
          have := hopnd_lt k hk_lt 1
          omega
        have h0_cond : opnd C k 0 < n ∨ (n ≤ opnd C k 0 ∧ InCone n C (opnd C k 0 - n) j) := by
          by_cases hlt : opnd C k 0 < n
          · exact Or.inl hlt
          · refine Or.inr ⟨by omega, hinCone_trans j (opnd C k 0 - n) k ?_ hcone⟩
            rw [hinCone_iff (opnd C k 0 - n) k hk_lt]
            exact ⟨opnd C k 0, by rw [hgate_ins k hk_lt]; exact List.mem_cons_self,
              by omega, hopnd_lt k hk_lt 0, Or.inl rfl⟩
        have h1_cond : opnd C k 1 < n ∨ (n ≤ opnd C k 1 ∧ InCone n C (opnd C k 1 - n) j) := by
          by_cases hlt : opnd C k 1 < n
          · exact Or.inl hlt
          · refine Or.inr ⟨by omega, hinCone_trans j (opnd C k 1 - n) k ?_ hcone⟩
            rw [hinCone_iff (opnd C k 1 - n) k hk_lt]
            exact ⟨opnd C k 1, by rw [hgate_ins k hk_lt]; exact List.mem_cons_of_mem _ List.mem_cons_self,
              by omega, hopnd_lt k hk_lt 1, Or.inl rfl⟩
        have ih0 := ih (opnd C k 0) h0_lt j hj h0_cond x
        have ih1 := ih (opnd C k 1) h1_lt j hj h1_cond x
        have heval : wireVal n C w x = (wireVal n C (opnd C k 0) x || wireVal n C (opnd C k 1) x) := by
          rw [hw_eq]
          exact hgate_or_eval k hk_lt hk_or x
        have horIn_mem (a : Fin n) : a ∈ orIn n C w ↔ a ∈ orIn n C (opnd C k 0) ∨ a ∈ orIn n C (opnd C k 1) := by
          rw [horIn_mem_def, horIn_mem_def, horIn_mem_def]
          constructor
          · intro h
            rcases h with heq | ⟨m, hm_lt, hm_reach, hm_or, hma⟩
            · exfalso
              have := a.isLt
              omega
            · rw [hw_eq, horReaches_iff k m hk_lt] at hm_reach
              rcases hm_reach with rfl | ⟨_, u, huin, hnu, hult, hureach⟩
              · rw [hgate_ins k hk_lt] at hma
                rcases List.mem_cons.mp hma with heq0 | hma'
                · exact Or.inl (Or.inl heq0)
                · rw [List.mem_singleton] at hma'
                  exact Or.inr (Or.inl hma')
              · rw [hgate_ins k hk_lt] at huin
                rcases List.mem_cons.mp huin with rfl | huin'
                · exact Or.inl (Or.inr ⟨m, hm_lt, hureach, hm_or, hma⟩)
                · rw [List.mem_singleton] at huin'
                  rw [huin'] at hureach
                  exact Or.inr (Or.inr ⟨m, hm_lt, hureach, hm_or, hma⟩)
          · intro h
            refine Or.inr ?_
            rcases h with h0 | h1
            · rcases h0 with heq0 | ⟨m, hm_lt, hm_reach, hm_or, hma⟩
              · refine ⟨k, hk_lt, ?_, hk_or, ?_⟩
                · rw [hw_eq, horReaches_iff k k hk_lt]; exact Or.inl rfl
                · rw [hgate_ins k hk_lt, heq0]; exact List.mem_cons_self
              · refine ⟨m, hm_lt, ?_, hm_or, hma⟩
                rw [hw_eq, horReaches_iff k m hk_lt]
                exact Or.inr ⟨hk_or, opnd C k 0, by rw [hgate_ins k hk_lt]; exact List.mem_cons_self,
                  hm_reach.1, hopnd_lt k hk_lt 0, hm_reach⟩
            · rcases h1 with heq1 | ⟨m, hm_lt, hm_reach, hm_or, hma⟩
              · refine ⟨k, hk_lt, ?_, hk_or, ?_⟩
                · rw [hw_eq, horReaches_iff k k hk_lt]; exact Or.inl rfl
                · rw [hgate_ins k hk_lt, heq1]; exact List.mem_cons_of_mem _ List.mem_cons_self
              · refine ⟨m, hm_lt, ?_, hm_or, hma⟩
                rw [hw_eq, horReaches_iff k m hk_lt]
                exact Or.inr ⟨hk_or, opnd C k 1, by rw [hgate_ins k hk_lt]; exact List.mem_cons_of_mem _ List.mem_cons_self,
                  hm_reach.1, hopnd_lt k hk_lt 1, hm_reach⟩
        rw [heval, Bool.or_eq_true, ih0, ih1]
        constructor
        · intro h
          rcases h with ⟨a, ha, hxa⟩ | ⟨a, ha, hxa⟩
          · exact ⟨a, (horIn_mem a).2 (Or.inl ha), hxa⟩
          · exact ⟨a, (horIn_mem a).2 (Or.inr ha), hxa⟩
        · intro h
          obtain ⟨a, ha, hxa⟩ := h
          rcases (horIn_mem a).1 ha with h0 | h1
          · exact Or.inl ⟨a, h0, hxa⟩
          · exact Or.inr ⟨a, h1, hxa⟩
  have hjunk_val_iff (j : ℕ) (hj : j ∈ junk G C) (x : Fin n → Bool) :
      gateVal n C j x = true ↔
        (∃ a ∈ side C j 0, x a = true) ∧ (∃ b ∈ side C j 1, x b = true) := by
    have hj_lt : j < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hj_and : (gateAt C j).op = GateOp.and := (Finset.mem_filter.mp hj).2.1
    rw [hgate_and_eval j hj_lt hj_and x, Bool.and_eq_true]
    have hside_cond (b : Fin 2) : opnd C j b < n ∨ (n ≤ opnd C j b ∧ InCone n C (opnd C j b - n) j) := by
      by_cases hlt : opnd C j b < n
      · exact Or.inl hlt
      · refine Or.inr ⟨by omega, ?_⟩
        rw [hinCone_iff (opnd C j b - n) j hj_lt]
        refine ⟨opnd C j b, ?_, by omega, hopnd_lt j hj_lt b, Or.inl rfl⟩
        rw [hgate_ins j hj_lt]
        fin_cases b
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ List.mem_cons_self
    have h0 := horIn_iff (opnd C j 0) j hj (hside_cond 0) x
    have h1 := horIn_iff (opnd C j 1) j hj (hside_cond 1) x
    exact and_congr h0 h1
  have hno_c4 (p1 p2 q1 q2 : Fin n) (hp : p1 ≠ p2) (hq : q1 ≠ q2)
      (h11 : G.Adj p1 q1) (h12 : G.Adj p1 q2) (h21 : G.Adj p2 q1) (h22 : G.Adj p2 q2) : False := by
    have hp1q1 : p1 ≠ q1 := G.ne_of_adj h11
    have hp1q2 : p1 ≠ q2 := G.ne_of_adj h12
    have hp2q1 : p2 ≠ q1 := G.ne_of_adj h21
    have hp2q2 : p2 ≠ q2 := G.ne_of_adj h22
    let w : G.Walk p1 p1 :=
      SimpleGraph.Walk.cons h11
        (SimpleGraph.Walk.cons h21.symm
          (SimpleGraph.Walk.cons h22
            (SimpleGraph.Walk.cons h12.symm SimpleGraph.Walk.nil)))
    have hcyc : w.IsCycle := by
      refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
      · change ([s(p1, q1), s(q1, p2), s(p2, q2), s(q2, p1)] : List (Sym2 (Fin n))).Nodup
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
          List.nodup_nil, not_false_eq_true, and_true]
        refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
        · intro h; rw [Sym2.eq_iff] at h; rcases h with ⟨h1, _⟩ | ⟨h1, _⟩; exact hp1q1 h1; exact hp h1
        · intro h; rw [Sym2.eq_iff] at h; rcases h with ⟨h1, _⟩ | ⟨h1, _⟩; exact hp h1; exact hp1q2 h1
        · intro h; rw [Sym2.eq_iff] at h; rcases h with ⟨h1, _⟩ | ⟨_, h2⟩; exact hp1q2 h1; exact hq h2
        · intro h; rw [Sym2.eq_iff] at h; rcases h with ⟨h1, _⟩ | ⟨h1, _⟩; exact hp2q1 h1.symm; exact hq h1
        · intro h; rw [Sym2.eq_iff] at h; rcases h with ⟨h1, _⟩ | ⟨h1, _⟩; exact hq h1; exact hp1q1 h1.symm
        · intro h; rw [Sym2.eq_iff] at h; rcases h with ⟨h1, _⟩ | ⟨h1, _⟩; exact hp2q2 h1; exact hp h1.symm
      · intro hnil
        have hlen := congrArg SimpleGraph.Walk.length hnil
        change 4 = 0 at hlen
        omega
      · change ([q1, p2, q2, p1] : List (Fin n)).Nodup
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
          List.nodup_nil, not_false_eq_true, and_true]
        exact ⟨⟨hp2q1.symm, hq, hp1q1.symm⟩, ⟨hp2q2, hp.symm⟩, hp1q2.symm⟩
    have h5 := hgirth p1 w hcyc
    have h4 : w.length = 4 := rfl
    omega
  have hgraphFun_pair (p q : Fin n) (h : graphFun G ∅ (pairInput p q) = true) : G.Adj p q := by
    change (decide (∃ a ∈ (∅ : Finset (Fin n)), pairInput p q a = true) ||
      decide (∃ x y, G.Adj x y ∧ pairInput p q x = true ∧ pairInput p q y = true)) = true at h
    rw [Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff] at h
    rcases h with ⟨a, ha, _⟩ | ⟨x, y, hxy, hx, hy⟩
    · cases ha
    · dsimp only [pairInput] at hx hy
      rw [decide_eq_true_iff] at hx hy
      have hne_xy : x ≠ y := G.ne_of_adj hxy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact (hne_xy rfl).elim
      · exact hxy
      · exact hxy.symm
      · exact (hne_xy rfl).elim
  let S := {e ∈ Ustar G C | ∃ (u v : Fin n), e = s(u, v) ∧
    ∃ t ∈ tops G C, ∃ j1 ∈ junk G C, ∃ j2 ∈ junk G C, j1 ≠ j2 ∧
      OrReaches n C (opnd C t 0) j1 ∧ OrReaches n C (opnd C t 1) j2 ∧
      gateVal n C j1 (pairInput u v) = true ∧ gateVal n C j2 (pairInput u v) = true}
  let P1 (e : Sym2 (Fin n)) : Prop := ∃ (u v : Fin n), e = s(u, v) ∧
    ∃ t ∈ tops G C, ∃ j1 ∈ junk G C, ∃ j2 ∈ junk G C, j1 ≠ j2 ∧
      ∃ b : Fin 2, OrReaches n C (opnd C t b) j1 ∧ OrReaches n C (opnd C t (1 - b)) j2 ∧
        u ∈ side C j1 0 ∧ u ∈ side C j1 1 ∧
        (u ∈ side C j2 0 ∨ v ∈ side C j2 0) ∧
        (u ∈ side C j2 1 ∨ v ∈ side C j2 1)
  let P2 (e : Sym2 (Fin n)) : Prop := ∃ (u v : Fin n), e = s(u, v) ∧
    ∃ t ∈ tops G C, ∃ j1 ∈ junk G C, ∃ j2 ∈ junk G C, j1 ≠ j2 ∧
      OrReaches n C (opnd C t 0) j1 ∧ OrReaches n C (opnd C t 1) j2 ∧
      ∃ b1 b2 : Fin 2, u ∈ side C j1 b1 ∧ u ∈ side C j2 b2 ∧
        v ∈ side C j1 (1 - b1) ∧ v ∈ side C j2 (1 - b2) ∧
        ∀ (w : Fin n), w ∈ side C j1 b1 → w ∈ side C j2 b2 → w = u
  let S1 := @Finset.filter (Sym2 (Fin n)) P1 (Classical.decPred P1) S
  let S2 := @Finset.filter (Sym2 (Fin n)) P2 (Classical.decPred P2) S
  have hsub : S ⊆ S1 ∪ S2 := by
    intro e he
    have he' := mem_fil.mp he
    obtain ⟨_, u, v, rfl, t, ht, j1, hj1, j2, hj2, hne12, hR0, hR1, hv1, hv2⟩ := he'
    have hj1_sides : (u ∈ side C j1 0 ∨ v ∈ side C j1 0) ∧ (u ∈ side C j1 1 ∨ v ∈ side C j1 1) := by
      have h := (hjunk_val_iff j1 hj1 (pairInput u v)).1 hv1
      obtain ⟨⟨a, ha, hpa⟩, ⟨b, hb, hpb⟩⟩ := h
      dsimp only [pairInput] at hpa hpb
      rw [decide_eq_true_iff] at hpa hpb
      constructor
      · rcases hpa with rfl | rfl
        · exact Or.inl ha
        · exact Or.inr ha
      · rcases hpb with rfl | rfl
        · exact Or.inl hb
        · exact Or.inr hb
    have hj2_sides : (u ∈ side C j2 0 ∨ v ∈ side C j2 0) ∧ (u ∈ side C j2 1 ∨ v ∈ side C j2 1) := by
      have h := (hjunk_val_iff j2 hj2 (pairInput u v)).1 hv2
      obtain ⟨⟨a, ha, hpa⟩, ⟨b, hb, hpb⟩⟩ := h
      dsimp only [pairInput] at hpa hpb
      rw [decide_eq_true_iff] at hpa hpb
      constructor
      · rcases hpa with rfl | rfl
        · exact Or.inl ha
        · exact Or.inr ha
      · rcases hpb with rfl | rfl
        · exact Or.inl hb
        · exact Or.inr hb
    rw [Finset.mem_union]
    by_cases hcase1 : (u ∈ side C j1 0 ∧ u ∈ side C j1 1) ∨ (v ∈ side C j1 0 ∧ v ∈ side C j1 1) ∨
        (u ∈ side C j2 0 ∧ u ∈ side C j2 1) ∨ (v ∈ side C j2 0 ∧ v ∈ side C j2 1)
    · left
      refine mem_fil.mpr ⟨he, ?_⟩
      rcases hcase1 with ⟨hu0, hu1⟩ | ⟨hv0, hv1'⟩ | ⟨hu0, hu1⟩ | ⟨hv0, hv1'⟩
      · exact ⟨u, v, rfl, t, ht, j1, hj1, j2, hj2, hne12, 0, hR0, hR1,
          hu0, hu1, hj2_sides.1, hj2_sides.2⟩
      · exact ⟨v, u, Sym2.eq_swap, t, ht, j1, hj1, j2, hj2, hne12, 0, hR0, hR1,
          hv0, hv1', hj2_sides.1.symm, hj2_sides.2.symm⟩
      · exact ⟨u, v, rfl, t, ht, j2, hj2, j1, hj1, hne12.symm, 1, hR1, hR0,
          hu0, hu1, hj1_sides.1, hj1_sides.2⟩
      · exact ⟨v, u, Sym2.eq_swap, t, ht, j2, hj2, j1, hj1, hne12.symm, 1, hR1, hR0,
          hv0, hv1', hj1_sides.1.symm, hj1_sides.2.symm⟩
    · right
      refine mem_fil.mpr ⟨he, ?_⟩
      have hb1_ex : ∃ b1 : Fin 2, u ∈ side C j1 b1 ∧ v ∈ side C j1 (1 - b1) := by
        rcases hj1_sides.1 with hu0 | hv0
        · rcases hj1_sides.2 with hu1 | hv1'
          · exact (hcase1 (Or.inl ⟨hu0, hu1⟩)).elim
          · exact ⟨0, hu0, hv1'⟩
        · rcases hj1_sides.2 with hu1 | hv1'
          · exact ⟨1, hu1, hv0⟩
          · exact (hcase1 (Or.inr (Or.inl ⟨hv0, hv1'⟩))).elim
      have hb2_ex : ∃ b2 : Fin 2, u ∈ side C j2 b2 ∧ v ∈ side C j2 (1 - b2) := by
        rcases hj2_sides.1 with hu0 | hv0
        · rcases hj2_sides.2 with hu1 | hv1'
          · exact (hcase1 (Or.inr (Or.inr (Or.inl ⟨hu0, hu1⟩)))).elim
          · exact ⟨0, hu0, hv1'⟩
        · rcases hj2_sides.2 with hu1 | hv1'
          · exact ⟨1, hu1, hv0⟩
          · exact (hcase1 (Or.inr (Or.inr (Or.inr ⟨hv0, hv1'⟩)))).elim
      obtain ⟨b1, hu1, hv1'⟩ := hb1_ex
      obtain ⟨b2, hu2, hv2'⟩ := hb2_ex
      let P : Finset (Fin n) := side C j1 b1 ∩ side C j2 b2
      let Q : Finset (Fin n) := side C j1 (1 - b1) ∩ side C j2 (1 - b2)
      have huP : u ∈ P := Finset.mem_inter.mpr ⟨hu1, hu2⟩
      have hvQ : v ∈ Q := Finset.mem_inter.mpr ⟨hv1', hv2'⟩
      have hbiclique (p q : Fin n) (hp : p ∈ P) (hq : q ∈ Q) : G.Adj p q := by
        have hp1 : p ∈ side C j1 b1 := (Finset.mem_inter.mp hp).1
        have hp2 : p ∈ side C j2 b2 := (Finset.mem_inter.mp hp).2
        have hq1 : q ∈ side C j1 (1 - b1) := (Finset.mem_inter.mp hq).1
        have hq2 : q ∈ side C j2 (1 - b2) := (Finset.mem_inter.mp hq).2
        have hp_in : pairInput p q p = true := by dsimp only [pairInput]; rw [decide_eq_true_iff]; exact Or.inl rfl
        have hq_in : pairInput p q q = true := by dsimp only [pairInput]; rw [decide_eq_true_iff]; exact Or.inr rfl
        have hgv1 : gateVal n C j1 (pairInput p q) = true := by
          rw [hjunk_val_iff j1 hj1 (pairInput p q)]
          fin_cases b1
          · exact ⟨⟨p, hp1, hp_in⟩, ⟨q, hq1, hq_in⟩⟩
          · exact ⟨⟨q, hq1, hq_in⟩, ⟨p, hp1, hp_in⟩⟩
        have hgv2 : gateVal n C j2 (pairInput p q) = true := by
          rw [hjunk_val_iff j2 hj2 (pairInput p q)]
          fin_cases b2
          · exact ⟨⟨p, hp2, hp_in⟩, ⟨q, hq2, hq_in⟩⟩
          · exact ⟨⟨q, hq2, hq_in⟩, ⟨p, hp2, hp_in⟩⟩
        have hw0 : wireVal n C (opnd C t 0) (pairInput p q) = true := by
          have hnw := hR0.1
          have heq : opnd C t 0 = n + (opnd C t 0 - n) := by omega
          rw [heq] at hR0 ⊢
          exact horReaches_true (opnd C t 0 - n) j1 (pairInput p q) hR0 hgv1
        have hw1 : wireVal n C (opnd C t 1) (pairInput p q) = true := by
          have hnw := hR1.1
          have heq : opnd C t 1 = n + (opnd C t 1 - n) := by omega
          rw [heq] at hR1 ⊢
          exact horReaches_true (opnd C t 1 - n) j2 (pairInput p q) hR1 hgv2
        have ht_lt : t < C.gates.length := Finset.mem_range.mp (mem_fil.mp ht).1
        have ht_and : (gateAt C t).op = GateOp.and := (mem_fil.mp ht).2.1
        have ht_bf : BelowF G C t := (mem_fil.mp ht).2.2
        have hgt : gateVal n C t (pairInput p q) = true := by
          rw [hgate_and_eval t ht_lt ht_and (pairInput p q), hw0, hw1]; rfl
        exact hgraphFun_pair p q (ht_bf (pairInput p q) hgt)
      by_cases hP_sing : ∀ p ∈ P, p = u
      · exact ⟨u, v, rfl, t, ht, j1, hj1, j2, hj2, hne12, hR0, hR1, b1, b2,
          hu1, hu2, hv1', hv2', fun w hw1 hw2 => hP_sing w (Finset.mem_inter.mpr ⟨hw1, hw2⟩)⟩
      · push Not at hP_sing
        obtain ⟨p', hp', hne_p⟩ := hP_sing
        have hQ_sing : ∀ q ∈ Q, q = v := by
          intro q hq
          by_contra hne_q
          exact hno_c4 u p' v q (Ne.symm hne_p) (Ne.symm hne_q)
            (hbiclique u v huP hvQ) (hbiclique u q huP hq)
            (hbiclique p' v hp' hvQ) (hbiclique p' q hp' hq)
        have hsub1 : 1 - (1 - b1) = b1 := by fin_cases b1 <;> rfl
        have hsub2 : 1 - (1 - b2) = b2 := by fin_cases b2 <;> rfl
        refine ⟨v, u, Sym2.eq_swap, t, ht, j1, hj1, j2, hj2, hne12, hR0, hR1, 1 - b1, 1 - b2,
          hv1', hv2', ?_, ?_, fun w hw1 hw2 => hQ_sing w (Finset.mem_inter.mpr ⟨hw1, hw2⟩)⟩
        · rw [hsub1]; exact hu1
        · rw [hsub2]; exact hu2
  have hcard1 : S1.card ≤ c1 * (C.size + 1) :=
    hc1 n G hgirth hne C hleast htop hjunk3 hno_jcone S1 (fun e he =>
      ⟨(mem_fil.mp (mem_fil.mp he).1).1, (mem_fil.mp he).2⟩)
  have hcard2 : S2.card ≤ c2 * (C.size + 1) :=
    hc2 n G hgirth hne C hleast htop hjunk3 hno_jcone S2 (fun e he =>
      ⟨(mem_fil.mp (mem_fil.mp he).1).1, (mem_fil.mp he).2⟩)
  have hle_union : S.card ≤ S1.card + S2.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le S1 S2)
  have hmul : (c1 + c2) * (C.size + 1) = c1 * (C.size + 1) + c2 * (C.size + 1) :=
    Nat.add_mul c1 c2 (C.size + 1)
  change S.card ≤ (c1 + c2) * (C.size + 1)
  omega
