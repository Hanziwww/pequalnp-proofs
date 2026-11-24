import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_4921_17
    (hClean : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      200 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (L l).card = q + 1) →
      (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ L l ∧ p2 ∈ L l) →
      have Comp : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun D =>
        ∀ z : Fin (N + N) → Bool,
          Fintype.card { l : Fin N // z (Fin.natAdd N l) = true } ≤ q →
          PEqualNP.MetaComplexity.circuitFun (N + N) D z =
            decide (∃ p l : Fin N, p ∈ L l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
      PEqualNP.MetaComplexity.Monotone2 C → Comp C →
      (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → Comp D → C.size ≤ D.size) →
      (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        ∀ z : Fin (N + N) → Bool,
          Fintype.card { l : Fin N // z (Fin.natAdd N l) = true } ≤ q →
          PEqualNP.EdgeOwnership.gateVal (N + N) C j z = true →
          PEqualNP.MetaComplexity.circuitFun (N + N) C z = true) →
      N * q ≤ 100 * C.size)
    (hDirtyOneHot : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      200 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (L l).card = q + 1) →
      (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ L l ∧ p2 ∈ L l) →
      have Comp : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun D =>
        ∀ z : Fin (N + N) → Bool,
          Fintype.card { l : Fin N // z (Fin.natAdd N l) = true } ≤ q →
          PEqualNP.MetaComplexity.circuitFun (N + N) D z =
            decide (∃ p l : Fin N, p ∈ L l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
      PEqualNP.MetaComplexity.Monotone2 C → Comp C →
      (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → Comp D → C.size ≤ D.size) →
      (∃ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        ∃ i : Fin (N + N), PEqualNP.EdgeOwnership.gateVal (N + N) C j (fun k => decide (k = i)) = true) →
      N * q ≤ 100 * C.size)
    (hDirtyNoOneHot : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      200 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (L l).card = q + 1) →
      (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ L l ∧ p2 ∈ L l) →
      have Comp : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun D =>
        ∀ z : Fin (N + N) → Bool,
          Fintype.card { l : Fin N // z (Fin.natAdd N l) = true } ≤ q →
          PEqualNP.MetaComplexity.circuitFun (N + N) D z =
            decide (∃ p l : Fin N, p ∈ L l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
      PEqualNP.MetaComplexity.Monotone2 C → Comp C →
      (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → Comp D → C.size ≤ D.size) →
      (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        ∀ i : Fin (N + N), PEqualNP.EdgeOwnership.gateVal (N + N) C j (fun k => decide (k = i)) = false) →
      (∃ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        ∃ z : Fin (N + N) → Bool,
          Fintype.card { l : Fin N // z (Fin.natAdd N l) = true } ≤ q ∧
          PEqualNP.EdgeOwnership.gateVal (N + N) C j z = true ∧
          PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) →
      N * q ≤ 100 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x10 : Fin (x2 + x2) → Bool), Fintype.card { x11 : Fin x2 // x10 (Fin.natAdd x2 x11) = Bool.true } ≤ x1 → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x4 x10 = Decidable.decide (∃ (x12 : Fin x2) (x13 : Fin x2), x12 ∈ x3 x13 ∧ x10 (Fin.castAdd x2 x12) = Bool.true ∧ x10 (Fin.natAdd x2 x13) = Bool.true)) → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), x11.size ≤ (100 : ℕ) * x4.size ∧ (∀ x12 ∈ x11.gates, x12.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x12.inputs.length ≤ (2 : ℕ)) ∧ ∀ (x12 : Fin x2), ∃ (x13 : ℕ), ∀ (x14 : Fin x2), (x11.wires (List.ofFn fun (x15 : Fin x2) => Decidable.decide (x15 = x14))).getD x13 Bool.false = Decidable.decide (x14 ∈ x3 x12) := by
  intro q N L C hq hN hcard huniq hmono hcomp
  let Comp : Circuit → Prop := fun D =>
    ∀ z : Fin (N + N) → Bool,
      Fintype.card { l : Fin N // z (Fin.natAdd N l) = true } ≤ q →
      circuitFun (N + N) D z =
        decide (∃ p l : Fin N, p ∈ L l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
  have hmin_ex : ∀ s : ℕ, ∀ C0 : Circuit, C0.size = s → Monotone2 C0 → Comp C0 →
      ∃ C' : Circuit, Monotone2 C' ∧ Comp C' ∧ C'.size ≤ C0.size ∧
        (∀ D : Circuit, Monotone2 D → Comp D → C'.size ≤ D.size) := by
    intro s
    induction s using Nat.strong_induction_on with
    | ind s ih =>
      intro C0 hsz hM0 hC0
      by_cases hmin : ∀ D : Circuit, Monotone2 D → Comp D → C0.size ≤ D.size
      · exact ⟨C0, hM0, hC0, Nat.le_refl _, hmin⟩
      · have hex : ∃ D : Circuit, Monotone2 D ∧ Comp D ∧ D.size < C0.size := by
          by_contra hnone
          apply hmin
          intro D hMD hCD
          by_contra hlt
          exact hnone ⟨D, hMD, hCD, by omega⟩
        obtain ⟨D, hMD, hCD, hDlt⟩ := hex
        obtain ⟨C', hMC', hCC', hC'le, hC'min⟩ := ih D.size (by omega) D rfl hMD hCD
        exact ⟨C', hMC', hCC', by omega, hC'min⟩
  obtain ⟨C', hMC', hCC', hC'le, hC'min⟩ := hmin_ex C.size C rfl hmono hcomp
  have hboundC' : N * q ≤ 100 * C'.size := by
    by_cases hcl : ∀ j < C'.gates.length, (gateAt C' j).op = GateOp.and →
        ∀ z : Fin (N + N) → Bool,
          Fintype.card { l : Fin N // z (Fin.natAdd N l) = true } ≤ q →
          gateVal (N + N) C' j z = true → circuitFun (N + N) C' z = true
    · exact hClean q N L C' hq hN hcard huniq hMC' hCC' hC'min hcl
    · have hdirty : ∃ j < C'.gates.length, (gateAt C' j).op = GateOp.and ∧
          ∃ z : Fin (N + N) → Bool,
            Fintype.card { l : Fin N // z (Fin.natAdd N l) = true } ≤ q ∧
            gateVal (N + N) C' j z = true ∧ circuitFun (N + N) C' z = false := by
        by_contra hnone
        apply hcl
        intro j hj hand z hz hgv
        by_contra hcf
        exact hnone ⟨j, hj, hand, z, hz, hgv, Bool.eq_false_iff.mpr hcf⟩
      by_cases hoh : ∃ j < C'.gates.length, (gateAt C' j).op = GateOp.and ∧
          ∃ i : Fin (N + N), gateVal (N + N) C' j (fun k => decide (k = i)) = true
      · exact hDirtyOneHot q N L C' hq hN hcard huniq hMC' hCC' hC'min hoh
      · have hno_oh : ∀ j < C'.gates.length, (gateAt C' j).op = GateOp.and →
            ∀ i : Fin (N + N), gateVal (N + N) C' j (fun k => decide (k = i)) = false := by
          intro j hj hand i
          by_contra ht
          exact hoh ⟨j, hj, hand, i, Bool.eq_true_of_not_eq_false ht⟩
        exact hDirtyNoOneHot q N L C' hq hN hcard huniq hMC' hCC' hC'min hno_oh hdirty
  have hbound : N * q ≤ 100 * C.size := by omega
  let step : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have eval_or (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have foldl_len : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g rest ih =>
      intro w
      simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
      omega
  have foldl_prefix : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl step w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g rest ih =>
      intro w i hi
      simp only [List.foldl_cons]
      rw [ih (step w g) i (by simp only [step, List.length_append, List.length_cons, List.length_nil]; omega)]
      exact List.getD_append _ _ _ _ hi
  let chainStep (st : List Gate × ℕ) (v : Fin N) : List Gate × ℕ :=
    (st.1 ++ [⟨GateOp.or, [st.2, v.val]⟩], N + st.1.length)
  have chain_props : ∀ (ts : List (Fin N)) (gs0 : List Gate) (acc0 : ℕ),
      acc0 < N + gs0.length →
      let res := ts.foldl chainStep (gs0, acc0)
      (∃ sfx : List Gate, res.1 = gs0 ++ sfx ∧ sfx.length = ts.length ∧
        ∀ g ∈ sfx, g.op = GateOp.or ∧ g.inputs.length ≤ 2) ∧
      res.2 < N + res.1.length ∧
      (∀ p : Fin N,
        let ep := List.ofFn (fun i : Fin N => decide (i = p))
        (res.1.foldl step ep).getD res.2 false = ((gs0.foldl step ep).getD acc0 false || decide (p ∈ ts))) := by
    intro ts
    induction ts with
    | nil =>
      intro gs0 acc0 hacc
      refine ⟨⟨[], by simp, rfl, fun _ h => by cases h⟩, hacc, ?_⟩
      intro p
      simp only [List.foldl_nil, List.not_mem_nil, decide_false, Bool.or_false]
    | cons v rest ih =>
      intro gs0 acc0 hacc
      let gNew : Gate := ⟨GateOp.or, [acc0, v.val]⟩
      let gs1 := gs0 ++ [gNew]
      let acc1 := N + gs0.length
      have hacc1 : acc1 < N + gs1.length := by
        simp only [acc1, gs1, List.length_append, List.length_cons, List.length_nil]; omega
      obtain ⟨⟨sfx2, hsfx2_eq, hsfx2_len, hsfx2_or⟩, hres_lt, hres_val⟩ := ih gs1 acc1 hacc1
      have hfold : (v :: rest).foldl chainStep (gs0, acc0) = rest.foldl chainStep (gs1, acc1) := rfl
      dsimp only
      rw [hfold]
      refine ⟨⟨gNew :: sfx2, by rw [hsfx2_eq]; simp [gs1], by simp [hsfx2_len], ?_⟩, hres_lt, ?_⟩
      · intro g hg
        rcases List.mem_cons.mp hg with rfl | h2
        · exact ⟨rfl, by simp [gNew]⟩
        · exact hsfx2_or g h2
      · intro p
        let ep := List.ofFn (fun i : Fin N => decide (i = p))
        have hstep1 : (gs1.foldl step ep).getD acc1 false =
            ((gs0.foldl step ep).getD acc0 false || decide (p = v)) := by
          dsimp only [gs1]
          rw [List.foldl_append]
          let w0 := gs0.foldl step ep
          have hw0_len : w0.length = acc1 := by
            simp only [w0, acc1, foldl_len, ep, List.length_ofFn]
          change (w0 ++ [GateOp.or.eval [w0.getD acc0 false, w0.getD v.val false]]).getD acc1 false = _
          rw [← hw0_len, List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)]
          simp only [Nat.sub_self, List.getElem_cons_zero, eval_or, List.any_cons, List.any_nil, id, Bool.or_false]
          have hv_val : w0.getD v.val false = decide (p = v) := by
            dsimp only [w0]
            rw [foldl_prefix gs0 ep v.val (by simp [ep, v.isLt]),
                List.getD_eq_getElem _ _ (by simp [ep, v.isLt])]
            simp only [ep, List.getElem_ofFn, Fin.eta, eq_comm]
          rw [hv_val]
        have hval := hres_val p
        dsimp only at hval
        rw [hval, hstep1, Bool.or_assoc]
        congr 1
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
  have allLines : ∀ (ls : List (Fin N)) (gs0 : List Gate),
      (∀ g ∈ gs0, g.op = GateOp.or ∧ g.inputs.length ≤ 2) →
      ∃ gs : List Gate,
        gs.length = gs0.length + ls.length * q ∧
        (∀ g ∈ gs, g.op = GateOp.or ∧ g.inputs.length ≤ 2) ∧
        (∀ l ∈ ls, ∃ w < N + gs.length, ∀ p : Fin N,
          (gs.foldl step (List.ofFn fun i : Fin N => decide (i = p))).getD w false = decide (p ∈ L l)) ∧
        (∃ sfx : List Gate, gs = gs0 ++ sfx) := by
    intro ls
    induction ls with
    | nil =>
      intro gs0 hgs0
      exact ⟨gs0, by simp, hgs0, fun _ h => (by cases h), ⟨[], by simp⟩⟩
    | cons l rest ih =>
      intro gs0 hgs0
      have hlen_L : (L l).toList.length = q + 1 := by
        rw [Finset.length_toList]; exact hcard l
      cases hto : (L l).toList with
      | nil => rw [hto] at hlen_L; simp at hlen_L
      | cons v0 ts =>
        have hts_len : ts.length = q := by
          rw [hto] at hlen_L; simp only [List.length_cons] at hlen_L; omega
        have hv0_lt : v0.val < N + gs0.length := by omega
        let res1 := ts.foldl chainStep (gs0, v0.val)
        obtain ⟨⟨sfx1, hsfx1_eq, hsfx1_len, hsfx1_or⟩, hw1_lt, hw1_val⟩ := chain_props ts gs0 v0.val hv0_lt
        have hgs1_or : ∀ g ∈ res1.1, g.op = GateOp.or ∧ g.inputs.length ≤ 2 := by
          intro g hg
          rw [hsfx1_eq] at hg
          rcases List.mem_append.mp hg with h1 | h2
          · exact hgs0 g h1
          · exact hsfx1_or g h2
        obtain ⟨gs, hgs_len, hgs_or, hgs_rest, ⟨sfx2, hsfx2_eq⟩⟩ := ih res1.1 hgs1_or
        have hgs1_len : res1.1.length = gs0.length + q := by
          rw [hsfx1_eq, List.length_append, hsfx1_len, hts_len]
        refine ⟨gs, ?_, hgs_or, ?_, ⟨sfx1 ++ sfx2, by rw [hsfx2_eq, hsfx1_eq, List.append_assoc]⟩⟩
        · rw [hgs_len, hgs1_len, List.length_cons, Nat.add_mul, Nat.one_mul]; omega
        · intro l' hl'
          rcases List.mem_cons.mp hl' with rfl | hrest'
          · refine ⟨res1.2, by change res1.2 < N + res1.1.length at hw1_lt; rw [hsfx2_eq, List.length_append]; omega, ?_⟩
            intro p
            let ep := List.ofFn (fun i : Fin N => decide (i = p))
            have hkeep : (gs.foldl step ep).getD res1.2 false = (res1.1.foldl step ep).getD res1.2 false := by
              rw [hsfx2_eq, List.foldl_append]
              exact foldl_prefix sfx2 (res1.1.foldl step ep) res1.2
                (by rw [foldl_len]; simp only [ep, List.length_ofFn]; exact hw1_lt)
            rw [hkeep]
            have hv := hw1_val p
            dsimp only at hv
            rw [hv]
            have hv0_val : (gs0.foldl step ep).getD v0.val false = decide (p = v0) := by
              rw [foldl_prefix gs0 ep v0.val (by simp [ep, v0.isLt]),
                  List.getD_eq_getElem _ _ (by simp [ep, v0.isLt])]
              simp only [ep, List.getElem_ofFn, Fin.eta, eq_comm]
            rw [hv0_val]
            apply Bool.eq_iff_iff.mpr
            simp only [Bool.or_eq_true, decide_eq_true_eq, ← Finset.mem_toList, hto, List.mem_cons]
          · exact hgs_rest l' hrest'
  obtain ⟨gs, hgs_len, hgs_or, hgs_all, _⟩ := allLines (List.finRange N) [] (fun _ h => by cases h)
  let D : Circuit := ⟨gs, 0⟩
  refine ⟨D, ?_, hgs_or, ?_⟩
  · change gs.length ≤ 100 * C.size
    rw [hgs_len, List.length_nil, Nat.zero_add, List.length_finRange]
    exact hbound
  · intro l
    obtain ⟨w, _, hw⟩ := hgs_all l (List.mem_finRange l)
    exact ⟨w, hw⟩
