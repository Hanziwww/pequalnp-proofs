import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The mask insertion follows Julleht (#9415) and the merged wiring argument in #7428.
-- L-meta-4308 pays for the binary gates. The remaining searches use ordinary circuit outputs.
set_option maxRecDepth 8000 in
set_option maxHeartbeats 9000000 in
theorem PEqualNP.Outside.R_meta_4643_73 :
  (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ))]) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (13 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => !x4.op.eval [Bool.false]) x1.gates) →
  (∀ Q : Circuit, FanInTwo Q → Q.size ≤ 14 →
    (∃ p t : Fin 9, p ≠ t ∧ ∀ x : Fin 9 → Bool,
      (Q.wires (List.ofFn x ++ [x 0 || x 6])).getD 10 false = (x p && x t)) →
    ∃ x : Fin 9 → Bool, Q.eval (List.ofFn x ++ [x 0 || x 6]) ≠
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e % 10)))) →
  (let F := fun (x : Fin 9 → Bool) => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e % 10)))
    let R := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 6]
    ∀ (v : Fin 9) (C : Circuit) (k : ℕ) (b : Bool),
      let w := fun x => (C.wires (R x)).getD k false
      v ≠ 0 → v ≠ 6 → FanInTwo C → C.size = 13 → 10 ≤ k → k < 22 →
      (C.gates.countP (fun g => g.op.eval [false]) ≤ 1) → (C.gates.take (k+1-10)).countP (fun g => g.op.eval [false]) = 0 →
      (∀ g ∈ C.gates.take (k+1-10), v.val ∉ g.inputs) →
      (∀ i j : Fin 9, i ≠ j → ∃ x : Fin 9 → Bool,
         (C.wires (R x)).getD 10 false ≠ (x i && x j)) →
      (∀ x, x v = false → F x = false → F (Function.update x v true) = true → w x = !b) →
      (∃ x, x v = !b ∧ w x = b ∧ C.eval (R x) ≠ F x) →
      ∃ x, (x v = b ∨ w x = !b) ∧ C.eval (R x) ≠ F x) →
  (let F := fun (x : Fin 9 → Bool) => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e % 10)))
    let R := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 6]
    ∀ (v : Fin 9) (C : Circuit) (k : ℕ) (b : Bool),
      let w := fun x => (C.wires (R x)).getD k false
      v ≠ 0 → v ≠ 6 → FanInTwo C → C.size = 13 → 10 ≤ k → k < 22 →
      (C.gates.countP (fun g => g.op.eval [false]) = 1) → (C.gates.drop (k+1-10)).countP (fun g => g.op.eval [false]) = 0 →
      (∀ g ∈ C.gates.take (k+1-10), v.val ∉ g.inputs) →
      (∀ i j : Fin 9, i ≠ j → ∃ x : Fin 9 → Bool,
         (C.wires (R x)).getD 10 false ≠ (x i && x j)) →
      (∀ x, x v = false → F x = false → F (Function.update x v true) = true → w x = !b) →
      (∃ x, x v = !b ∧ w x = b ∧ C.eval (R x) ≠ F x) →
      (∀ x, C.eval (R x) ≠ F x → F x = b) →
      ∃ x, (x v = b ∨ w x = !b) ∧ C.eval (R x) ≠ F x) →
  have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → (Fin (9 : ℕ) → Bool) → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : Fin (9 : ℕ) → Bool) => (x3.wires (x2 x5)).getD x4 Bool.false; ∀ (x4 : Fin (9 : ℕ)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ) (x7 : Bool), x4 ≠ (0 : Fin (9 : ℕ)) → x4 ≠ (6 : Fin (9 : ℕ)) → PEqualNP.MetaComplexity.FanInTwo x5 → x5.size = (13 : ℕ) → x5.output = (22 : ℕ) → (10 : ℕ) ≤ x6 → x6 < (22 : ℕ) → (x7 = Bool.false → x6 = (10 : ℕ) → x4 = (1 : Fin (9 : ℕ)) ∨ x4 = (4 : Fin (9 : ℕ)) ∨ x4 = (7 : Fin (9 : ℕ))) → (∀ x16 ∈ List.take (x6 + (1 : ℕ) - (10 : ℕ)) x5.gates, ↑x4 ∉ x16.inputs) → (∀ (x17 x18 : Fin (9 : ℕ) → Bool), (∀ (x19 : Fin (9 : ℕ)), x19 ≠ x4 → x17 x19 = x18 x19) → x1 x17 ≠ x1 x18 → x3 x5 x6 x17 = !x7) → (∃ x18 ∈ x5.gates, (9 : ℕ) ∈ x18.inputs) → (∃ (x19 : Fin (9 : ℕ) → Bool), x19 x4 = !x7 ∧ x3 x5 x6 x19 = x7 ∧ x5.eval (x2 x19) ≠ x1 x19) → ∃ (x20 : Fin (9 : ℕ) → Bool), x5.eval ((x2 x20).set (↑x4) (if x7 = Bool.true then x20 x4 || x3 x5 x6 x20 else x20 x4 && x3 x5 x6 x20)) ≠ x1 x20 := by
  intro binary rawAnd early late
  let isNot := fun (g : Gate) => g.op.eval [false]
  let target (x : Fin 9 → Bool) : Bool :=
    ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))

  let row (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 6]

  let emit (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  let maskBit (x h disj : Bool) := if disj then x || h else x && h

  let redirect (v k i : ℕ) : ℕ := if i = v then k else if i < k then i else i+1

  let rename (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

  have fold_size (gs : List Gate) (w : List Bool) : (gs.foldl emit w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons,ih]; simp [emit]; omega

  have fold_preserves (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl emit w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih (emit w g) (by simp [emit]; omega)]
      exact List.getD_append _ _ _ _ hi

  have set_emit_avoid (g : Gate) (w : List Bool) (v : ℕ) (val : Bool)
      (hv : v < w.length) (avoid : v ∉ g.inputs) :
      emit (w.set v val) g = (emit w g).set v val := by
    have reads : ∀ i ∈ g.inputs, (w.set v val).getD i false = w.getD i false := by
      intro i hi
      have ne : v ≠ i := by intro eq; apply avoid; exact eq ▸ hi
      by_cases valid : i < w.length
      · rw [List.getD_eq_getElem _ _ (by simpa using valid),List.getD_eq_getElem _ _ valid,
          List.getElem_set_ne ne]
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt valid),
          List.getD_eq_default _ _ (Nat.le_of_not_gt valid)]
    unfold emit
    rw [List.map_congr_left reads,List.set_append_left v val hv]

  have fold_set_avoid (gs : List Gate) (w : List Bool) (v : ℕ) (val : Bool)
      (hv : v < w.length) (avoid : ∀ g ∈ gs, v ∉ g.inputs) :
      gs.foldl emit (w.set v val) = (gs.foldl emit w).set v val := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [set_emit_avoid g w v val hv (avoid g (by simp))]
      exact ih (emit w g) (by simp [emit]; omega) (fun a ha => avoid a (by simp [ha]))

  have append_other (w : List Bool) (b : Bool) (i : ℕ) (ne : i ≠ w.length) :
      (w++[b]).getD i false = w.getD i false := by
    by_cases small : i < w.length
    · exact List.getD_append _ _ _ _ small
    · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]

  have suffix_shift (gs : List Gate) (v k : ℕ) (w y : List Bool)
      (hv : v < k) (hk : k ≤ w.length) (len : y.length = w.length + 1)
      (rel : ∀ i, y.getD (redirect v k i) false = w.getD i false) :
      ∀ i, ((gs.map (rename (redirect v k))).foldl emit y).getD (redirect v k i) false =
        (gs.foldl emit w).getD i false := by
    induction gs generalizing w y with
    | nil => exact rel
    | cons g gs ih =>
      simp only [List.map_cons,List.foldl_cons]
      let value := g.op.eval (g.inputs.map fun i => w.getD i false)
      have emitY : emit y (rename (redirect v k) g) = y ++ [value] := by
        change y ++ [g.op.eval ((g.inputs.map (redirect v k)).map fun i => y.getD i false)] = _
        simp only [List.map_map,Function.comp_def]
        rw [List.map_congr_left (fun i _ => rel i)]
      rw [emitY]
      apply ih (w++[value]) (y++[value])
      · simp; omega
      · simp [len]
      intro i
      have sameWire : redirect v k i = y.length ↔ i = w.length := by
        by_cases eq : i = v
        · simp only [redirect]
          rw [ite_eq_left eq]
          omega
        · simp only [redirect]
          rw [ite_eq_right eq]
          split <;> omega
      by_cases hi : i = w.length
      · rw [sameWire.mpr hi,hi]
        simp
      · rw [append_other _ _ _ (fun a => hi (sameWire.mp a)),append_other _ _ _ hi]
        exact rel i

  have append_with_mask (v : ℕ) (old : List Bool) (hv : v < old.length) (bit : Bool) :
      ∀ i, (old ++ [bit]).getD (redirect v old.length i) false = (old.set v bit).getD i false := by
    intro i
    by_cases piv : i = v
    · subst i
      simp only [redirect, ite_true]
      rw [List.getD_append_right _ _ _ _ le_rfl,Nat.sub_self,List.getD_cons_zero,
        List.getD_eq_getElem _ _ (by simp; exact hv)]
      simp
    simp only [redirect]
    rw [ite_eq_right piv]
    by_cases valid : i < old.length
    · rw [ite_eq_left valid,List.getD_append _ _ _ _ valid,List.getD_eq_getElem _ _ valid,
        List.getD_eq_getElem _ _ (by simpa using valid),List.getElem_set_ne (Ne.symm piv)]
    · rw [ite_eq_right valid,List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]

  have row_pivot (x : Fin 9 → Bool) (v : Fin 9) : (row x).getD v.val false = x v := by
    unfold row
    rw [List.getD_append _ _ _ _ (by simpa using v.isLt),
      List.getD_eq_getElem _ _ (by simpa using v.isLt),List.getElem_ofFn]

  have mask_value (x : Fin 9 → Bool) (v : Fin 9) (k : ℕ) (disj : Bool) (old : List Bool)
      (hv : v.val < old.length) (oldv : old.getD v.val false = x v) :
      emit old ⟨if disj then .or else .and,[v.val,k]⟩ =
        old ++ [maskBit (x v) (old.getD k false) disj] := by
    unfold emit maskBit
    cases disj
    · change old ++ [(old.getD v.val false && (old.getD k false && true))] =
        old ++ [x v && old.getD k false]
      rw [Bool.and_true,oldv]
    · change old ++ [(old.getD v.val false || (old.getD k false || false))] =
        old ++ [x v || old.getD k false]
      rw [Bool.or_false,oldv]

  have insertMasked (C : Circuit) (v : Fin 9) (k : ℕ) (disj : Bool)
      (fan : FanInTwo C) (lo : 10 ≤ k) (hi : k < 10+C.size)
      (avoid : ∀ g ∈ C.gates.take (k+1-10), v.val ∉ g.inputs) :
      ∃ Q : Circuit, FanInTwo Q ∧ Q.size = C.size+1 ∧ Q.gates.countP isNot = C.gates.countP isNot ∧
        (∀ x : Fin 9 → Bool, (Q.wires (row x)).getD 10 false = (C.wires (row x)).getD 10 false) ∧
        ∀ x : Fin 9 → Bool, Q.eval (row x) = C.eval
          ((row x).set v.val (maskBit (x v) ((C.wires (row x)).getD k false) disj)) := by
    let pre := C.gates.take (k+1-10)
    let suf := C.gates.drop (k+1-10)
    let mask : Gate := ⟨if disj then .or else .and,[v.val,k]⟩
    let shift := rename (redirect v.val (k+1))
    let D : Circuit := ⟨(pre ++ mask :: suf.map shift),redirect v.val (k+1) C.output⟩
    have split : pre ++ suf = C.gates := List.take_append_drop _ _
    have maskLegal : mask.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ mask.inputs.length ≤ 2 := by
      cases disj <;> simp [mask]
    have legal : FanInTwo D := by
      intro g hg
      change g ∈ (pre ++ mask :: suf.map shift) at hg
      rcases List.mem_append.mp hg with hg | hg
      · exact fan g (by rw [← split]; exact List.mem_append_left _ hg)
      rcases List.mem_cons.mp hg with rfl | hg
      · exact maskLegal
      obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hg
      obtain ⟨op,arity⟩ := fan g' (by rw [← split]; exact List.mem_append_right _ hg')
      exact ⟨op,by simpa [shift,rename] using arity⟩
    have hsize : D.size = C.size+1 := by
      have len := congrArg List.length split
      change ((pre ++ mask :: suf.map shift)).length = C.gates.length+1
      simp only [List.length_cons,List.length_append,List.length_map] at len ⊢
      omega
    have cn : D.gates.countP isNot = C.gates.countP isNot := by
      change (pre ++ mask :: suf.map shift).countP isNot = _
      rw [← split,List.countP_append,List.countP_append,List.countP_cons]
      have transformed : (suf.map shift).countP isNot = suf.countP isNot := by
        rw [List.countP_map]
        rfl
      have m : isNot mask = false := by cases disj <;> rfl
      simp [m,transformed]
    have firstWire (x : Fin 9 → Bool) : (D.wires (row x)).getD 10 false = (C.wires (row x)).getD 10 false := by
      have kb : k+1-10 ≤ C.gates.length := by change k < 10+C.gates.length at hi; omega
      have ln : (pre.foldl emit (row x)).length = k+1 := by
        rw [fold_size]
        simp [pre,row,kb]
        omega
      change ((pre ++ mask :: suf.map shift).foldl emit (row x)).getD 10 false =
        (C.gates.foldl emit (row x)).getD 10 false
      rw [← split,List.foldl_append,List.foldl_append,
          fold_preserves (mask :: suf.map shift) _ _ (by omega),
          fold_preserves suf _ _ (by omega)]
    refine ⟨D,legal,hsize,cn,firstWire,?_⟩
    intro x
    let old := pre.foldl emit (row x)
    have kBound : k+1-10 ≤ C.gates.length := by change k < 10+C.gates.length at hi; omega
    have length : old.length = k+1 := by
      rw [show old = pre.foldl emit (row x) by rfl,fold_size]
      simp [pre,row,Nat.min_eq_left kBound]
      omega
    have vBound : v.val < old.length := by rw [length]; have := v.isLt; omega
    have saved : (C.wires (row x)).getD k false = old.getD k false := by
      change (C.gates.foldl emit (row x)).getD k false = _
      rw [← split,List.foldl_append]
      exact fold_preserves suf old k (by omega)
    have savedV : old.getD v.val false = x v := by
      rw [fold_preserves pre (row x) _ (by simp [row]; have := v.isLt; omega),row_pivot]
    let bit := maskBit (x v) (old.getD k false) disj
    have oldSet : pre.foldl emit ((row x).set v.val bit) = old.set v.val bit :=
      fold_set_avoid pre (row x) v.val bit (by simp [row]; have := v.isLt; omega) avoid
    have law (i : ℕ) : (old ++ [bit]).getD (redirect v.val (k+1) i) false =
        (old.set v.val bit).getD i false := by rw [← length]; exact append_with_mask v.val old vBound bit i
    have simulated := suffix_shift suf v.val (k+1) (old.set v.val bit) (old++[bit])
      (by have := v.isLt; omega) (by simp [length]) (by simp) law C.output
    change ((pre ++ mask :: suf.map shift).foldl emit (row x)).getD
        (redirect v.val (k+1) C.output) false =
      (C.gates.foldl emit ((row x).set v.val (maskBit (x v) ((C.wires (row x)).getD k false) disj))).getD C.output false
    rw [List.foldl_append, List.foldl_cons,mask_value x v k disj old vBound savedV,
      saved,← split,List.foldl_append,oldSet]
    exact simulated

  have evalAnd (w : List Bool) : GateOp.and.eval w = w.all id := rfl
  have evalOr (w : List Bool) : GateOp.or.eval w = w.any id := rfl
  let wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

  have getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
    simp

  have gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
      (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
      (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
      op.eval l₁ = true → op.eval l₂ = true := by
    rcases hop with rfl | rfl
    · simp only [evalAnd, List.all_eq_true, id_eq]
      intro h b hb
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
      have h1 : l₁.getD i false = true := by
        have hi1 : i < l₁.length := by omega
        rw [List.getD_eq_getElem _ _ hi1]
        exact h _ (List.getElem_mem hi1)
      have h2 := hle i h1
      rwa [List.getD_eq_getElem _ _ hi] at h2
    · simp only [evalOr, List.any_eq_true, id_eq]
      rintro ⟨b, hb, rfl⟩
      obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
      have h1 : l₁.getD i false = true := by
        rw [List.getD_eq_getElem _ _ hi]; exact hbi
      have h2 := hle i h1
      have hi2 : i < l₂.length := by omega
      rw [List.getD_eq_getElem _ _ hi2] at h2
      exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

  have wiresFrom_mono (gs : List Gate)
      (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
      ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
        (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
        ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
    induction gs with
    | nil =>
      intro w₁ w₂ _ hle i hi
      exact hle i hi
    | cons g gs ih =>
      intro w₁ w₂ hlen hle i hi
      have hstep1 : wiresFrom (g :: gs) w₁ =
          wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
      have hstep2 : wiresFrom (g :: gs) w₂ =
          wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
      rw [hstep1] at hi
      rw [hstep2]
      apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
      intro j hj
      by_cases hlt : j < w₁.length
      · rw [List.getD_append _ _ _ _ hlt] at hj
        rw [List.getD_append _ _ _ _ (by omega)]
        exact hle j hj
      · by_cases heq : j = w₁.length
        · subst heq
          rw [getD_snoc_eq] at hj
          rw [hlen, getD_snoc_eq]
          exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
            (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
            (by simp) (by
              intro t ht
              by_cases ht_lt : t < g.inputs.length
              · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
                rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
                simp only [List.getElem_map] at ht ⊢
                exact hle _ ht
              · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
                exact Bool.noConfusion ht) hj
        · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
          exact Bool.noConfusion hj
  have count (gs : List Gate) :
      gs.countP (fun g => !isNot g) + gs.countP isNot = gs.length := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.countP_cons,List.length_cons]
      cases isNot g <;> simp <;> omega
  dsimp only at ⊢
  intro v C k b v0 v6 fan size _ lo hi _ blind sens _ miss
  let w := fun x => (C.wires (row x)).getD k false
  have sizeof : C.gates.length = 13 := size
  let pre := C.gates.take (k+1-10)
  let suf := C.gates.drop (k+1-10)
  have split : pre ++ suf = C.gates := List.take_append_drop _ _
  by_contra! correct
  change ∀ x, C.eval ((row x).set v.val (maskBit (x v) (w x) b)) = target x at correct
  obtain ⟨Q,qfan,qsize,qnot,firstQ,simulation⟩ := insertMasked C v k b fan lo (by omega) blind
  have cq (x : Fin 9 → Bool) : Q.eval (row x) = target x := (simulation x).trans (correct x)
  have noRaw (i j : Fin 9) (ne : i ≠ j) :
      ∃ x : Fin 9 → Bool, (C.wires (row x)).getD 10 false ≠ (x i && x j) := by
    by_contra! always
    obtain ⟨x,err⟩ := rawAnd Q qfan (by omega)
      ⟨i,j,ne,fun x => (firstQ x).trans (always x)⟩
    exact err (cq x)
  have lb := binary Q qfan (fun x => by
    rw [show Q.eval (List.ofFn x ++ [x 0 || x 6]) = target x from cq x]
    simp only [target,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc] <;> rfl)
  change 13 ≤ Q.gates.countP (fun g => !isNot g) at lb
  have qlen : Q.gates.length = 14 := by change Q.size = 14; omega
  have qtotal := count Q.gates
  have one : C.gates.countP isNot ≤ 1 := by omega
  have parts : pre.countP isNot + suf.countP isNot = C.gates.countP isNot := by
    rw [← List.countP_append,split]
  have pivot (x : Fin 9 → Bool) (_ : x v = false) (base : target x = false)
      (changed : target (Function.update x v true) = true) : w x = !b := by
    apply sens x (Function.update x v true)
    · intro j jv
      exact (Function.update_of_ne jv true x).symm
    · change target x ≠ target (Function.update x v true)
      rw [base,changed]
      decide
  have stable (x : Fin 9 → Bool) (condition : x v = b ∨ w x = !b) : C.eval (row x) = target x := by
    have bit : maskBit (x v) (w x) b = x v := by
      rcases condition with h|h <;> cases b <;> simp [maskBit,h]
    have same : (row x).set v.val (x v) = row x := by
      have valid : v.val < (row x).length := by simp [row]; have := v.isLt; omega
      have h : (row x)[v.val] = x v := by
        rw [← List.getD_eq_getElem _ false valid,row_pivot]
      rw [← h,List.set_getElem_self]
    have hx := correct x
    simpa only [bit,same] using hx
  have witness : ∃ x, (x v = b ∨ w x = !b) ∧ C.eval (row x) ≠ target x := by
    by_cases hp : pre.countP isNot = 0
    · exact early v C k b v0 v6 fan size lo hi one hp blind noRaw pivot miss
    have hs : suf.countP isNot = 0 := by omega
    have onlyOne : C.gates.countP isNot = 1 := by omega
    have suffix (g : Gate) (mem : g ∈ suf) : g.op = .and ∨ g.op = .or := by
      have ok := (fan g (by rw [← split]; exact List.mem_append_right _ mem)).1
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ok
      rcases ok with a|o|n
      · exact Or.inl a
      · exact Or.inr o
      · have no := List.countP_eq_zero.mp hs g mem
        have yes : isNot g = true := by change g.op.eval [false] = true; rw [n]; rfl
        simp [yes] at no
    have side (x : Fin 9 → Bool) (err : C.eval (row x) ≠ target x) : target x = b := by
      let old := pre.foldl emit (row x)
      let m := maskBit (x v) (w x) b
      have len : v.val < (row x).length := by simp [row]; have := v.isLt; omega
      have olen : v.val < old.length := by
        change v.val < (pre.foldl emit (row x)).length
        rw [fold_size]; omega
      have ov : old.getD v.val false = x v := (fold_preserves pre _ _ len).trans (row_pivot x v)
      have preEq : pre.foldl emit ((row x).set v.val m) = old.set v.val m :=
        fold_set_avoid pre (row x) v.val m len blind
      have ordinary : C.eval (row x) = (wiresFrom suf old).getD C.output false := by
        change (C.gates.foldl emit (row x)).getD C.output false = _
        rw [← split,List.foldl_append]
      have masked : (wiresFrom suf (old.set v.val m)).getD C.output false = target x := by
        have h := correct x
        change (C.gates.foldl emit ((row x).set v.val m)).getD C.output false = _ at h
        rw [← split,List.foldl_append,preEq] at h
        exact h
      have same (i : ℕ) (ne : i ≠ v.val) : (old.set v.val m).getD i false = old.getD i false := by
        by_cases within : i < old.length
        · rw [List.getD_eq_getElem _ _ (by simpa using within),List.getD_eq_getElem _ _ within,
            List.getElem_set_ne (Ne.symm ne)]
        · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt within),
            List.getD_eq_default _ _ (Nat.le_of_not_lt within)]
      have atv : (old.set v.val m).getD v.val false = m := by
        rw [List.getD_eq_getElem _ _ (by simpa using olen),List.getElem_set_self]
      cases bb : b with
      | false =>
        apply Bool.eq_false_iff.mpr
        intro on
        have test := wiresFrom_mono suf suffix (old.set v.val m) old (by simp) (by
          intro i hi
          by_cases ne : i ≠ v.val
          · rwa [same i ne] at hi
          · have e : i = v.val := not_ne_iff.mp ne
            subst i
            rw [atv] at hi
            rw [ov]
            cases hval : x v <;> simp [m,maskBit,bb,hval] at hi ⊢)
          C.output (masked.trans on)
        exact err ((ordinary.trans test).trans on.symm)
      | true =>
        cases hx : target x with
        | true => rfl
        | false =>
          have on : C.eval (row x) = true := by
            cases e : C.eval (row x) with
            | false => exact False.elim (err (e.trans hx.symm))
            | true => rfl
          have test := wiresFrom_mono suf suffix old (old.set v.val m) (by simp) (by
            intro i hi
            by_cases ne : i ≠ v.val
            · rwa [same i ne]
            · have e : i = v.val := not_ne_iff.mp ne
              subst i
              rw [atv]
              rw [ov] at hi
              simp only [m,maskBit,bb,↓reduceIte,hi,Bool.true_or])
            C.output (ordinary.symm.trans on)
          exact Bool.noConfusion ((masked.trans hx).symm.trans test)
    exact late v C k b v0 v6 fan size lo hi onlyOne hs blind noRaw pivot miss side
  obtain ⟨x,neutral,diff⟩ := witness
  exact diff (stable x neutral)
