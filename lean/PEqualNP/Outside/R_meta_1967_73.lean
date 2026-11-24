import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The normalization premise is the one in R_meta_1480_873.
-- A signed rectangle weight proves rigidity for the Fano formula case:
-- a leaf covering a diagonal flag covers its whole three-by-three star.
set_option maxRecDepth 18000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_1967_73
    (normalize : let inc := fun p l : Fin 7 => p=l ∨ p=l+1 ∨ p=l+3
      let valid := fun C : Circuit => C.size ≤ 27 ∧ (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j) ∧
        ∀ x : Fin 14 → Bool, C.eval (List.ofFn x)=true ↔ ∃ p l : Fin 7, inc p l ∧
          x (Fin.castAdd 7 p)=true ∧ x (Fin.natAdd 7 l)=true
      let tree := fun C : Circuit => ((C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (14≤w))).Nodup
      ∀ (C : Circuit) (p l : Fin 7), valid C → inc p l →
        2≤C.lineDeg 14 {p.val} → 2≤C.lineDeg 14 {7+l.val} →
        ∃ D : Circuit, valid D ∧ tree D ∧ 2≤D.lineDeg 14 {p.val} ∧ 2≤D.lineDeg 14 {7+l.val})
    (treePartition : ∀ (n k : ℕ) (C : Circuit) (X Z : Fin k → Fin n → Bool),
      PEqualNP.TopForm.IsAO2 n C →
      (∀ g ∈ C.gates, g.inputs.Nodup) → C.eval (List.replicate n true) = true →
      ((C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (n≤w))).Nodup →
      (∀ i, circuitFun n C (X i) = true ∧ circuitFun n C (Z i) = false) →
      ∃ (m : ℕ) (label : Fin m → Fin n) (A B : Fin m → Finset (Fin k)),
        m ≤ C.size+1 ∧
        (∀ j, (∀ e ∈ A j, X e (label j) = true) ∧ (∀ f ∈ B j, Z f (label j) = false)) ∧
        (∀ e f, ∃! j, e ∈ A j ∧ f ∈ B j) ∧
        ∀ v : Fin n, C.lineDeg n {v.val} ≤ Fintype.card {j : Fin m // label j = v}) :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ∧ ∃ (x2 : ℕ) (x3 : ℕ), (PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 x3 ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x3 x2) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x2 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ (∀ (x4 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x4) (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ))) = Bool.false) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x3 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x3 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x3 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ ∀ (x4 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x3 x4) (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.false := by
  let scan {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
    gs.foldl (fun w g => w ++ [step w g]) w

  have scan_cons {α : Type} (step : List α → Gate → α) (g : Gate) (gs : List Gate) (w : List α) :
      scan step (g :: gs) w = scan step gs (w ++ [step w g]) := rfl

  have scan_append {α : Type} (step : List α → Gate → α) (gs hs : List Gate) (w : List α) :
      scan step (gs ++ hs) w = scan step hs (scan step gs w) := by
    simp [scan, List.foldl_append]

  have scan_length {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) :
      (scan step gs w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih => rw [scan_cons, ih]; simp; omega

  have scan_prefix {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
      (d : α) (i : ℕ) (hi : i < w.length) :
      (scan step gs w).getD i d = w.getD i d := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [scan_cons, ih _ (by simp; omega)]
      exact List.getD_append _ _ _ _ hi

  have read_gate {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
      (d : α) (j : ℕ) (hj : j < gs.length) (a b : ℕ)
      (ha : a < w.length + j) (hb : b < w.length + j) (op : α → α → α)
      (hstep : ∀ p, step p gs[j] = op (p.getD a d) (p.getD b d)) :
      (scan step gs w).getD (w.length + j) d =
        op ((scan step gs w).getD a d) ((scan step gs w).getD b d) := by
    let pre := scan step (gs.take j) w
    have hp : pre.length = w.length + j := by
      simp [pre, scan_length, Nat.min_eq_left hj.le]
    have hs : scan step gs w = scan step (gs[j] :: gs.drop (j+1)) pre := by
      have hsplit := List.take_append_drop j gs
      conv_lhs => rw [← hsplit, scan_append, List.drop_eq_getElem_cons hj]
    have hpre (i : ℕ) (hi : i < w.length + j) : (scan step gs w).getD i d = pre.getD i d := by
      rw [hs]
      exact scan_prefix _ _ _ _ _ (by omega)
    rw [hpre a ha, hpre b hb, hs, scan_cons, scan_prefix _ _ _ _ _ (by simp [hp]),
      List.getD_append_right _ _ _ _ (by omega)]
    simpa [hp] using hstep pre

  let gateValue (w : List Bool) (g : Gate) : Bool :=
    g.op.eval (g.inputs.map fun i => w.getD i false)

  have inputValue (C : Circuit) (x : Fin 14 → Bool) (i : Fin 14) :
      (C.wires (List.ofFn x)).getD i.val false = x i := by
    change (scan gateValue C.gates (List.ofFn x)).getD i.val false = _
    rw [scan_prefix _ _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

  have valueAt (C : Circuit) (x : Fin 14 → Bool) (j : ℕ) (hj : j < C.gates.length)
      (a b : ℕ) (ha : a < 14 + j) (hb : b < 14 + j)
      (op : Bool → Bool → Bool)
      (h : ∀ w, gateValue w C.gates[j] = op (w.getD a false) (w.getD b false)) :
      (C.wires (List.ofFn x)).getD (14+j) false =
        op ((C.wires (List.ofFn x)).getD a false) ((C.wires (List.ofFn x)).getD b false) := by
    change (scan gateValue C.gates (List.ofFn x)).getD (14+j) false =
      op ((scan gateValue C.gates (List.ofFn x)).getD a false)
        ((scan gateValue C.gates (List.ofFn x)).getD b false)
    simpa only [List.length_ofFn] using
      read_gate gateValue C.gates (List.ofFn x) false j hj a b
        (by simpa only [List.length_ofFn] using ha) (by simpa only [List.length_ofFn] using hb) op h

  let inputDegrees (p : Fin 14) : List ℕ :=
    (List.range 14).map fun i => if i ∈ ({p.val} : Finset ℕ) then 1 else 0

  have inputDegree (C : Circuit) (p : Fin 14) (i : ℕ) (hi : i < 14) :
      (C.lineDegrees 14 {p.val}).getD i 0 = if i = p.val then 1 else 0 := by
    change (scan (fun w g => g.lineDegree w) C.gates (inputDegrees p)).getD i 0 = _
    rw [scan_prefix _ _ _ _ _ (by simpa [inputDegrees] using hi),
      List.getD_eq_getElem _ _ (by simpa [inputDegrees] using hi)]
    simp [inputDegrees]

  have degreeAt (C : Circuit) (p : Fin 14) (j : ℕ) (hj : j < C.gates.length)
      (a b : ℕ) (ha : a < 14 + j) (hb : b < 14 + j) (op : ℕ → ℕ → ℕ)
      (h : ∀ w, C.gates[j].lineDegree w = op (w.getD a 0) (w.getD b 0)) :
      (C.lineDegrees 14 {p.val}).getD (14+j) 0 =
        op ((C.lineDegrees 14 {p.val}).getD a 0) ((C.lineDegrees 14 {p.val}).getD b 0) := by
    change (scan (fun w g => g.lineDegree w) C.gates (inputDegrees p)).getD (14+j) 0 =
      op ((scan (fun w g => g.lineDegree w) C.gates (inputDegrees p)).getD a 0)
        ((scan (fun w g => g.lineDegree w) C.gates (inputDegrees p)).getD b 0)
    have hlen : (inputDegrees p).length = 14 := by simp [inputDegrees]
    simpa only [hlen] using
      read_gate (fun w g => g.lineDegree w) C.gates (inputDegrees p) 0 j hj a b
        (by simpa [hlen] using ha) (by simpa [hlen] using hb) op h


  have markedDegree (C : Circuit) (k : ℕ) (u v : Fin 14) (well : PEqualNP.TopForm.IsAO2 14 C)
      (kind : (NestedCover.gateAt C k).op = .and)
      (live : 14+k=C.output ∨ PEqualNP.EdgeOwnership.InCone 14 C k (C.output-14))
      (high : PEqualNP.EdgeOwnership.gateVal 14 C k (PEqualNP.EdgeOwnership.pairInput u v) = true)
      (low : ∀ b : Fin 2, PEqualNP.CleanedNonEdge.wireVal 14 C (PEqualNP.TopForm.opnd C k b)
        (PEqualNP.EdgeOwnership.pairInput u u) = false) : 2 ≤ C.lineDeg 14 {v.val} := by
    have cones_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (cs : List (List ℕ)),
        (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) cs).length = cs.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro cs; simp
      | cons g gs ih =>
        intro cs
        rw [List.foldl_cons, ih]
        dsimp only [PEqualNP.EdgeOwnership.coneStep]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
    have cones_char : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (i j : ℕ),
        i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []).getD j [] ↔
          j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs,
            14 ≤ w ∧ w < 14 + j ∧
            (i = w - 14 ∨ i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []).getD (w - 14) []) := by
      intro gs
      induction gs using List.reverseRecOn with
      | nil => intro i j; simp
      | append_singleton gs g ih =>
        intro i j
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        have hlen : (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []).length = gs.length := by
          rw [cones_len]; simp
        have key : ∀ k, k < gs.length →
            (PEqualNP.EdgeOwnership.coneStep 14 (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []) g).getD k [] =
              (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []).getD k [] := by
          intro k hk
          dsimp only [PEqualNP.EdgeOwnership.coneStep]
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left (by omega)]
        rcases Nat.lt_trichotomy j gs.length with h | h | h
        · have e1 : (gs ++ [g]).getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ =
              gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by
            simp only [List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_left h]
          rw [key j h, ih i j, e1]
          constructor
          · rintro ⟨_, w, hw, h1, h2, h3⟩
            refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
            rw [key (w - 14) (by omega)]; exact h3
          · rintro ⟨_, w, hw, h1, h2, h3⟩
            refine ⟨h, w, hw, h1, h2, ?_⟩
            rw [key (w - 14) (by omega)] at h3; exact h3
        · subst h
          have e1 : (gs ++ [g]).getD gs.length ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = g := by
            simp [List.getD_eq_getElem?_getD]
          have e2 : (PEqualNP.EdgeOwnership.coneStep 14
              (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []) g).getD gs.length [] =
              (g.inputs.filter (fun w => decide (14 ≤ w ∧ w < 14 + gs.length))).flatMap
                (fun w => (w - 14) :: (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []).getD (w - 14) []) := by
            dsimp only [PEqualNP.EdgeOwnership.coneStep]
            simp only [List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by omega)]
            simp [hlen]
          rw [e1, e2, List.mem_flatMap]
          constructor
          · rintro ⟨w, hw, hmem⟩
            rw [List.mem_filter, decide_eq_true_eq] at hw
            refine ⟨by simp, w, hw.1, hw.2.1, hw.2.2, ?_⟩
            rw [key (w - 14) (by omega)]
            simpa using hmem
          · rintro ⟨_, w, hw, h1, h2, h3⟩
            rw [key (w - 14) (by omega)] at h3
            exact ⟨w, List.mem_filter.mpr ⟨hw, decide_eq_true ⟨h1, h2⟩⟩, by simpa using h3⟩
        · have e3 : (PEqualNP.EdgeOwnership.coneStep 14
              (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []) g).getD j [] = [] := by
            apply List.getD_eq_default
            dsimp only [PEqualNP.EdgeOwnership.coneStep]
            simp only [List.length_append, List.length_singleton, hlen]
            omega
          rw [e3]
          simp only [List.not_mem_nil, false_iff, not_and]
          intro hlt
          simp only [List.length_append, List.length_singleton] at hlt
          omega
    have inCone_iff : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (i j : ℕ),
        PEqualNP.EdgeOwnership.InCone 14 D i j ↔
          j < D.gates.length ∧ ∃ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs,
            14 ≤ w ∧ w < 14 + j ∧ (i = w - 14 ∨ PEqualNP.EdgeOwnership.InCone 14 D i (w - 14)) :=
      fun D i j => cones_char D.gates i j
    let x := PEqualNP.EdgeOwnership.pairInput u u
    let y := PEqualNP.EdgeOwnership.pairInput u v
    let val (z : Fin 14 → Bool) (i : ℕ) := (C.wires (List.ofFn z)).getD i false
    let deg (i : ℕ) := (C.lineDegrees 14 {v.val}).getD i 0
    have shape (j : ℕ) (hj : j < C.gates.length) : ∃ a b : ℕ,
        C.gates[j].inputs = [a,b] ∧ a<14+j ∧ b<14+j ∧
        ((C.gates[j].op = .and ∧ (∀ z, val z (14+j) = (val z a && val z b)) ∧ deg (14+j) = deg a+deg b) ∨
        (C.gates[j].op = .or ∧ (∀ z, val z (14+j) = (val z a || val z b)) ∧ deg (14+j) = max (deg a) (deg b))) := by
      let g := C.gates[j]
      have mem : g ∈ C.gates := List.getElem_mem _
      obtain ⟨a,b,pins⟩ := List.length_eq_two.mp (well.2.2 _ mem)
      have pinEq : NestedCover.gateAt C j = g := List.getD_eq_getElem _ _ hj
      have earlier (w : ℕ) (hw : w ∈ [a,b]) : w < 14+j := well.2.1 j hj w (by rwa [pinEq,pins])
      have ha := earlier a (by simp)
      have hb := earlier b (by simp)
      refine ⟨a,b,pins,ha,hb,?_⟩
      rcases well.1 g mem with op|op
      · refine Or.inl ⟨op,?_,?_⟩
        · intro z
          apply valueAt C z j hj a b ha hb Bool.and
          intro w
          change g.op.eval (g.inputs.map _) = _
          rw [op,pins]
          change (w.getD a false && (w.getD b false && true)) = _
          simp
        · apply degreeAt C v j hj a b ha hb Nat.add
          intro w
          change g.lineDegree w = _
          have ge : g = ⟨GateOp.and,[a,b]⟩ :=
            (show g = ⟨g.op,g.inputs⟩ from rfl).trans (by rw [op,pins])
          rw [ge]
          change w.getD a 0 + (w.getD b 0 + 0) = _
          simp
      · refine Or.inr ⟨op,?_,?_⟩
        · intro z
          apply valueAt C z j hj a b ha hb Bool.or
          intro w
          change g.op.eval (g.inputs.map _) = _
          rw [op,pins]
          change (w.getD a false || (w.getD b false || false)) = _
          simp
        · apply degreeAt C v j hj a b ha hb Nat.max
          intro w
          change g.lineDegree w = _
          have ge : g = ⟨GateOp.or,[a,b]⟩ :=
            (show g = ⟨g.op,g.inputs⟩ from rfl).trans (by rw [op,pins])
          rw [ge]
          change max (w.getD a 0) (max (w.getD b 0) 0) = _
          simp
    have neutral (i : ℕ) (hi : i < 14+C.gates.length) (zero : deg i=0) : val x i = val y i := by
      induction i using Nat.strong_induction_on with
      | ind i ih =>
        by_cases small : i<14
        · let p : Fin 14 := ⟨i,small⟩
          have ne : i ≠ v.val := by
            intro eq
            have d := inputDegree C v i small
            change deg i = _ at d
            rw [if_pos eq] at d
            omega
          have pn : p ≠ v := fun e => ne (congrArg Fin.val e)
          change (C.wires (List.ofFn x)).getD p.val false = (C.wires (List.ofFn y)).getD p.val false
          rw [inputValue C x p,inputValue C y p]
          change decide (p=u ∨ p=u) = decide (p=u ∨ p=v)
          simp [pn]
        · let j := i-14
          have eq : i = 14+j := by dsimp [j]; omega
          obtain ⟨a,b,_,ha,hb,caseAnd|caseOr⟩ := shape j (by omega)
          · obtain ⟨_,vals,degs⟩ := caseAnd
            have d : deg a+deg b=0 := by rw [←degs,←eq]; exact zero
            rw [eq,vals,vals,ih a (by omega) (by omega) (by omega),ih b (by omega) (by omega) (by omega)]
          · obtain ⟨_,vals,degs⟩ := caseOr
            have d : max (deg a) (deg b) = 0 := by rw [← degs, ← eq]; exact zero
            have da := le_max_left (deg a) (deg b)
            have db := le_max_right (deg a) (deg b)
            rw [eq,vals,vals,ih a (by omega) (by omega) (by omega),ih b (by omega) (by omega) (by omega)]
    have hk : k<C.gates.length := by
      by_contra! late
      change (C.gates.getD k _).op = .and at kind
      rw [List.getD_eq_default _ _ late] at kind
      cases kind
    have actual : NestedCover.gateAt C k = C.gates[k] := List.getD_eq_getElem _ _ hk
    obtain ⟨a,b,pins,ha,hb,caseAnd|caseOr⟩ := shape k hk
    · obtain ⟨_,vals,degs⟩ := caseAnd
      have value : (val y a && val y b)=true := (vals y).symm.trans high
      have off (s : Fin 2) : val x (([a,b] : List ℕ).getD s.val 0) = false := by
        have h := low s
        change val x ((NestedCover.gateAt C k).inputs.getD s.val 0) = false at h
        rwa [actual,pins] at h
      have offA : val x a = false := off 0
      have offB : val x b = false := off 1
      have pa : 0<deg a := by
        by_contra! bad
        have e := neutral a (by omega) (by omega)
        have wrong := offA.symm.trans (e.trans (Bool.and_eq_true_iff.mp value).1)
        cases wrong
      have pb : 0<deg b := by
        by_contra! bad
        have e := neutral b (by omega) (by omega)
        have wrong := offB.symm.trans (e.trans (Bool.and_eq_true_iff.mp value).2)
        cases wrong
      have here : 2 ≤ deg (14+k) := by omega
      have up (s j : ℕ) (reach : PEqualNP.EdgeOwnership.InCone 14 C s j) : deg (14+s) ≤ deg (14+j) := by
        induction j using Nat.strong_induction_on with
        | ind j ih =>
          obtain ⟨hj,w,mem,gate,lt,direct|prior⟩ := (inCone_iff C s j).mp reach
          all_goals
            have gateAt : NestedCover.gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
            obtain ⟨a,b,pins,_,_,laws⟩ := shape j hj
            rw [gateAt,pins] at mem
            have one : deg w ≤ deg (14+j) := by
              rcases List.mem_cons.mp mem with e|e
              · subst w
                rcases laws with h|h
                · rw [h.2.2]; omega
                · rw [h.2.2]; exact le_max_left _ _
              · have same := List.mem_singleton.mp e
                subst w
                rcases laws with h|h
                · rw [h.2.2]; omega
                · rw [h.2.2]; exact le_max_right _ _
          · simpa only [show 14+s=w by omega] using one
          · have prev := ih (w-14) (by omega) prior
            rw [show 14+(w-14)=w by omega] at prev
            exact prev.trans one
      change 2 ≤ deg C.output
      rcases live with gate|path
      · simpa only [←gate] using here
      · obtain ⟨_,w,_,lo,top,_⟩ := (inCone_iff C k (C.output-14)).mp path
        have res := here.trans (up _ _ path)
        rwa [show 14+(C.output-14)=C.output by omega] at res
    · have bad := caseOr.1
      rw [actual,bad] at kind
      cases kind
  let pt (e : Fin 21) : ℕ := (e.val/3 + ([0,1,3] : List ℕ).getD (e.val % 3) 0) % 7
  let ln (e : Fin 21) : ℕ := e.val/3
  let onLine (p l : ℕ) : Bool := decide (p=l ∨ p=(l+1)%7 ∨ p=(l+3)%7)
  let yesRow (e : Fin 21) (v : Fin 14) := decide (v.val=pt e ∨ v.val=7+ln e)
  let noRow (f : Fin 21) (v : Fin 14) :=
    if v.val < 7 then onLine v.val (ln f) && decide (v.val ≠ pt f)
    else onLine (pt f) (v.val-7) && decide (v.val-7 ≠ ln f)
  let star (v : Fin 14) := Finset.univ.filter fun e => yesRow e v = true
  let cell (e f : Fin 21) : ℤ := if e=f then -4 else if pt e=pt f ∨ ln e=ln f then 3 else 0
  let weight (A B : Finset (Fin 21)) : ℤ := ∑ e ∈ A, ∑ f ∈ B, cell e f

  have certificates :
      (∀ v : Fin 14, (star v).card = 3) ∧
      (∀ (v : Fin 14) (e f : Fin 21), e ∈ star v → noRow f v = false → f ∉ star v → cell e f = 0) ∧
      (∀ (v : Fin 14) (e f : Fin 21), e ∈ star v → f ∈ star v →
        cell e f = 3 - (if f=e then (7:ℤ) else 0)) ∧
      (∑ e : Fin 21, ∑ f : Fin 21, cell e f) = 168 := by
    dsimp only [star,pt,ln,onLine,yesRow,noRow,cell]
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    decide +kernel

  have local_score (v : Fin 14) (A B : Finset (Fin 21)) (pa : A ⊆ star v)
      (nb : ∀ f ∈ B, noRow f v = false) :
      weight A B = 3*(A.card:ℤ)*(B ∩ star v).card - 7*((A ∩ (B ∩ star v)).card:ℤ) := by
    classical
    let K := B ∩ star v
    have row (e : Fin 21) (he : e ∈ A) :
        (∑ f ∈ B, cell e f) = 3*(K.card:ℤ) - (if e ∈ K then 7 else 0) := by
      have restrict : (∑ f ∈ B, cell e f) = ∑ f ∈ K, cell e f := by
        symm
        apply Finset.sum_subset Finset.inter_subset_left
        intro f hf out
        exact certificates.2.1 v e f (pa he) (nb f hf) (fun hs => out (Finset.mem_inter.mpr ⟨hf,hs⟩))
      rw [restrict]
      calc
        _ = ∑ f ∈ K, (3 - (if f=e then (7:ℤ) else 0)) :=
          Finset.sum_congr rfl fun f hf => certificates.2.2.1 v e f (pa he) (Finset.mem_inter.mp hf).2
        _ = _ := by rw [Finset.sum_sub_distrib]; simp [mul_comm]
    have count : (∑ e ∈ A, if e∈K then (7:ℤ) else 0) = 7*((A ∩ K).card:ℤ) := by
      rw [← Finset.sum_filter]
      simp [Finset.filter_mem_eq_inter,mul_comm]
    unfold weight
    rw [Finset.sum_congr rfl row,Finset.sum_sub_distrib,count,Finset.sum_const,nsmul_eq_mul]
    change (A.card:ℤ)*(3*(K.card:ℤ)) - _ = 3*(A.card:ℤ)*(K.card:ℤ) - _
    ring

  have rectangle_scale (a b c : ℕ) (ha : a ≤ 3) (hb : b ≤ 3) (ca : c ≤ a) (cb : c ≤ b)
      (cap : a+b ≤ 3+c) :
      3*(a:ℤ)*b-7*c ≤ 6 ∧
      (3*(a:ℤ)*b-7*c = 6 → 0<a ∧ 0<b ∧ (0<c → a=3 ∧ b=3)) := by
    interval_cases a <;> interval_cases b <;> omega

  have leaf_score (v : Fin 14) (A B : Finset (Fin 21)) (pa : A ⊆ star v)
      (nb : ∀ f ∈ B, noRow f v = false) :
      weight A B ≤ 6 ∧ (weight A B = 6 → A.Nonempty ∧ (B ∩ star v).Nonempty ∧
        (∀ e, e ∈ A → e ∈ B → star v ⊆ A ∧ star v ⊆ B)) := by
    let K := B ∩ star v
    have pk : K ⊆ star v := Finset.inter_subset_right
    have upper := Finset.card_le_card (Finset.union_subset pa pk)
    rw [certificates.1 v] at upper
    have sum := Finset.card_union_add_card_inter A K
    have bound := rectangle_scale A.card K.card (A ∩ K).card
      ((Finset.card_le_card pa).trans_eq (certificates.1 v))
      ((Finset.card_le_card pk).trans_eq (certificates.1 v))
      (Finset.card_le_card Finset.inter_subset_left) (Finset.card_le_card Finset.inter_subset_right) (by omega)
    have eq := local_score v A B pa nb
    change weight A B = 3*(A.card:ℤ)*K.card-7*((A ∩ K).card:ℤ) at eq
    refine ⟨eq ▸ bound.1,?_⟩
    intro six
    obtain ⟨aa,bb,rigid⟩ := bound.2 (eq.symm.trans six)
    refine ⟨Finset.card_pos.mp aa,Finset.card_pos.mp bb,?_⟩
    intro e ha hb
    have both : e ∈ A ∩ K := Finset.mem_inter.mpr ⟨ha,Finset.mem_inter.mpr ⟨hb,pa ha⟩⟩
    obtain ⟨hA,hB⟩ := rigid (Finset.card_pos.mpr ⟨e,both⟩)
    have equalA := Finset.eq_of_subset_of_card_le pa (by rw [hA,certificates.1])
    have equalB := Finset.eq_of_subset_of_card_le pk (by rw [hB,certificates.1])
    exact ⟨equalA ▸ Finset.Subset.rfl, equalB ▸ (show K ⊆ B from Finset.inter_subset_left)⟩

  have sum_partition {m : ℕ} (A B : Fin m → Finset (Fin 21))
      (one : ∀ e f : Fin 21, ∃! j : Fin m, e ∈ A j ∧ f ∈ B j) :
      (∑ j, weight (A j) (B j)) = 168 := by
    classical
    let entry (j : Fin m) (e f : Fin 21) : ℤ := if e ∈ A j ∧ f ∈ B j then cell e f else 0
    have expand (j : Fin m) : weight (A j) (B j) = ∑ e, ∑ f, entry j e f := by
      simp only [weight,entry,ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero]
      simp [← Finset.sum_filter]
    have total (e f : Fin 21) : ∑ j, entry j e f = cell e f := by
      obtain ⟨i,hi,uniq⟩ := one e f
      rw [Finset.sum_eq_single i]
      · simp [entry,hi]
      · intro j _ ne
        exact if_neg (fun h => ne (uniq j h))
      · simp
    calc
      _ = ∑ j, ∑ e, ∑ f, entry j e f := Finset.sum_congr rfl fun j _ => expand j
      _ = ∑ e, ∑ j, ∑ f, entry j e f := Finset.sum_comm
      _ = ∑ e, ∑ f, ∑ j, entry j e f :=
        Finset.sum_congr rfl fun e _ => Finset.sum_comm
      _ = ∑ e, ∑ f, cell e f := by simp only [total]
      _ = _ := certificates.2.2.2

  have fano_rectangle_rigidity (m : ℕ) (label : Fin m → Fin 14) (A B : Fin m → Finset (Fin 21))
      (left : ∀ j, A j ⊆ star (label j)) (right : ∀ j f, f ∈ B j → noRow f (label j) = false)
      (one : ∀ e f : Fin 21, ∃! j : Fin m, e ∈ A j ∧ f ∈ B j) :
      28 ≤ m ∧ (m ≤ 28 → ∀ e : Fin 21, ∃ v : Fin 14, yesRow e v = true ∧ ∃! j : Fin m, label j = v) := by
    classical
    have bound (j : Fin m) := leaf_score (label j) (A j) (B j) (left j) (right j)
    have total := sum_partition A B one
    have all : (∑ j, weight (A j) (B j)) ≤ ∑ _j : Fin m, (6:ℤ) :=
      Finset.sum_le_sum fun j _ => (bound j).1
    have cost : (∑ _j : Fin m, (6:ℤ)) = (m:ℤ)*6 := by simp
    rw [total,cost] at all
    refine ⟨by omega,?_⟩
    intro max e
    have tight (j : Fin m) : weight (A j) (B j) = 6 := by
      by_contra! ne
      have strict : (∑ i, weight (A i) (B i)) < ∑ _i : Fin m,(6:ℤ) := by
        apply Finset.sum_lt_sum (fun i _ => (bound i).1)
        exact ⟨j,Finset.mem_univ _,lt_of_le_of_ne (bound j).1 ne⟩
      rw [total,cost] at strict
      omega
    obtain ⟨j,⟨ej,fj⟩,_⟩ := one e e
    obtain ⟨wholeA,wholeB⟩ := ((bound j).2 (tight j)).2.2 e ej fj
    have mem := left j ej
    refine ⟨label j,(Finset.mem_filter.mp mem).2,j,rfl,?_⟩
    intro k same
    obtain ⟨⟨a,ak⟩,⟨f,fk⟩,_⟩ := (bound k).2 (tight k)
    have aStar : a ∈ star (label j) := same ▸ left k ak
    have fStar : f ∈ star (label j) := same ▸ (Finset.mem_inter.mp fk).2
    exact (one a f).unique ⟨ak,(Finset.mem_inter.mp fk).1⟩ ⟨wholeA aStar,wholeB fStar⟩
  let incident (p l : Fin 7) := p=l ∨ p=l+1 ∨ p=l+3
  have positives : ∀ e : Fin 21, ∃ p l : Fin 7, incident p l ∧
      yesRow e (Fin.castAdd 7 p) = true ∧ yesRow e (Fin.natAdd 7 l) = true := by
    dsimp only [incident,yesRow,pt,ln]
    decide +kernel
  have negatives : ∀ f : Fin 21, ¬ ∃ p l : Fin 7, incident p l ∧
      noRow f (Fin.castAdd 7 p) = true ∧ noRow f (Fin.natAdd 7 l) = true := by
    dsimp only [incident,noRow,pt,ln,onLine]
    decide +kernel
  have flagZero : ∀ v : Fin 14, yesRow 0 v = true → v=0 ∨ v=7 := by
    dsimp only [yesRow,pt,ln]
    decide +kernel
  have ao (D : Circuit) (shape : ∀ (j : ℕ) (g : Gate), D.gates[j]? = some g →
      (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a<14+j ∧ b<14+j) :
      PEqualNP.TopForm.IsAO2 14 D := by
    refine ⟨?_,?_,?_⟩
    · intro g mem
      obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp mem
      exact (shape j _ (List.getElem?_eq_getElem hj)).1
    · intro j hj t hmem
      obtain ⟨a,b,pins,_,ha,hb⟩ := (shape j _ (List.getElem?_eq_getElem hj)).2
      change t ∈ (D.gates.getD j _).inputs at hmem
      rw [List.getD_eq_getElem _ _ hj,pins] at hmem
      rcases List.mem_cons.mp hmem with h|h
      · simpa [h] using ha
      · simpa [List.mem_singleton.mp h] using hb
    · intro g mem
      obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp mem
      obtain ⟨a,b,pins,_⟩ := (shape j _ (List.getElem?_eq_getElem hj)).2
      simp [pins]
  rintro ⟨C,small,shape,works,k,j,_,opk,livek,yesk,nok,opj,livej,yesj,noj⟩
  have same : PEqualNP.EdgeOwnership.pairInput (7 : Fin 14) 0 =
      PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7 := by
    funext u
    change decide (u=7 ∨ u=0) = decide (u=0 ∨ u=7)
    simp only [or_comm]
  have line := markedDegree C k 0 7 (ao C shape) opk livek yesk nok
  have point := markedDegree C j 7 0 (ao C shape) opj livej (same ▸ yesj) noj
  obtain ⟨D,⟨sz,legal,exactD⟩,tree,dp,dl⟩ := normalize C 0 0
    ⟨small,shape,works⟩ (Or.inl rfl) point line
  have rows (t : Fin 21) :
      circuitFun 14 D (yesRow t) = true ∧ circuitFun 14 D (noRow t) = false := by
    refine ⟨(exactD _).mpr (positives t),?_⟩
    cases h : circuitFun 14 D (noRow t) with
    | false => rfl
    | true => exact False.elim (negatives t ((exactD _).mp h))
  have distinct (g : Gate) (hg : g ∈ D.gates) : g.inputs.Nodup := by
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hg
    obtain ⟨a,b,pins,ne,_⟩ := (legal i _ (List.getElem?_eq_getElem hi)).2
    simp [pins,ne]
  have full : D.eval (List.replicate 14 true) = true := by
    have h := (exactD (fun _ => true)).mpr ⟨0,0,Or.inl rfl,rfl,rfl⟩
    simpa only [List.ofFn_const] using h
  obtain ⟨m,lab,A,B,budget,ok,unique,degrees⟩ := treePartition 14 21 D yesRow noRow (ao D legal) distinct full tree rows
  have pos (i : Fin m) : A i ⊆ star (lab i) := fun e he => Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,(ok i).1 e he⟩
  obtain ⟨_,rigid⟩ := fano_rectangle_rigidity m lab A B pos (fun i => (ok i).2) unique
  obtain ⟨v,hv,i,eq,alone⟩ := rigid (by omega) 0
  have single : Finset.univ.filter (fun k : Fin m => lab k=v) = {i} := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    exact ⟨alone k,fun h => h ▸ eq⟩
  have once := degrees v
  rw [Fintype.card_subtype,single,Finset.card_singleton] at once
  rcases flagZero v hv with rfl|rfl
  · change 2 ≤ D.lineDeg 14 {0} at dp
    change D.lineDeg 14 {0} ≤ 1 at once
    omega
  · change 2 ≤ D.lineDeg 14 {7} at dl
    change D.lineDeg 14 {7} ≤ 1 at once
    omega
