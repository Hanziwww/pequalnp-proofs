import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

-- Costs zero and one distinguish proofs with zero or one marked leaf.
-- Boolean tests use costs zero and two. The final two tests charge a
-- marked leaf one, so the same gate operations check the derivative rows.
-- Four successive fourteen-bit boundary masks are stored in each list entry.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 12000000 in
theorem PEqualNP.Outside.R_meta_2346_91
    (geometry : let adj (i j : Fin 14) := (([10368,4480,8960,1664,3328,6656,13312,11,22,44,88,49,98,69] : List ℕ).getD i.val 0).testBit j.val
      ∀ a b : Fin 14, a ≠ b → ∃ π : Equiv.Perm (Fin 14),
        ((π 0 = 0 ∧ π 7 = 7) ∨ (π 0 = 7 ∧ π 7 = 0)) ∧
        (∀ i j, adj (π i) (π j) = adj i j) ∧
        14*min (π a).val (π b).val + max (π a).val (π b).val ∈ ([1,2,7,8,11,16,17,22,23,25,32,34,36,38] : List ℕ))
    (excluded :
      let table : List ℕ := [573945371705473,2269461860090114,4538923588132868,2393091369861392,18296165611604000,1587760290848832,3663766027026912,6768946055808039,11549907977570382,18666416739814336,25901471711383817,36805067917039628,42364467165831464,56931619210045450,266352904]
      let start (r : Fin 60) (i : Fin 14) : ℕ :=
        if r.val < 58 then
          if (table.getD (r.val / 4) 0).testBit (14 * (r.val % 4) + i.val) then 0 else 2
        else if i.val = (if r.val=58 then 0 else 7) then 0
        else if i.val = (if r.val=58 then 7 else 0) then 1 else 2
      ∀ (P : List.Vector (Fin 41 × Fin 41 × Bool) 27) (o : Fin 41),
        (∀ j : Fin 27, let g := P.get j
          g.1.val < 14+j.val ∧ g.2.1.val < 14+j.val ∧ g.1 ≠ g.2.1) →
        (P.get 0).2.2 = true →
        (14*min (P.get 0).1.val (P.get 0).2.1.val +
          max (P.get 0).1.val (P.get 0).2.1.val ∈ ([1,2,7,8,11,16,17,22,23,25,32,34,36,38] : List ℕ)) →
        ∃ r : Fin 60, ((P.toList.foldl (fun (w : List ℕ) g =>
          let a := w.getD g.1.val 2
          let b := w.getD g.2.1.val 2
          w ++ [cond g.2.2 (min 2 (a+b)) (min a b)]) (List.ofFn (start r))).getD o.val 2)
          ≠ (if r.val < 21 then 0 else 2)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and →           (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →             (∀ (x7 : Bool),                 ∃ (x8 : ℕ → Bool),                   have x9 : List Bool := x1.wires (List.ofFn fun (x9 : Fin (14 : ℕ)) => Decidable.decide (x9 = if x7 = Bool.true then (0 : Fin (14 : ℕ)) else (7 : Fin (14 : ℕ))));                   (∀ x10 < (14 : ℕ), x8 x10 = Decidable.decide (x10 = if x7 = Bool.true then (7 : ℕ) else (0 : ℕ))) ∧                     (∀ x10 < x1.size,                         have x12 : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10;                         have x13 : ℕ := PEqualNP.TopForm.opnd x1 x10 (0 : Fin (2 : ℕ));                         have x14 : ℕ := PEqualNP.TopForm.opnd x1 x10 (1 : Fin (2 : ℕ));                         (x12.op = PEqualNP.CircuitLowerBounds.GateOp.and → x8 ((14 : ℕ) + x10) = (x9.getD x13 Bool.false && x8 x14 || x8 x13 && x9.getD x14 Bool.false)) ∧ (x12.op = PEqualNP.CircuitLowerBounds.GateOp.or → x8 ((14 : ℕ) + x10) = (x8 x13 || x8 x14))) ∧                       x8 x1.output = Bool.false) →               False := by
  let adj (i j : Fin 14) := (([10368,4480,8960,1664,3328,6656,13312,11,22,44,88,49,98,69] : List ℕ).getD i.val 0).testBit j.val
  let target (x : Fin 14 → Bool) := ∃ i j : Fin 14, adj i j = true ∧ x i = true ∧ x j = true
  let inc (p l : Fin 7) := p=l ∨ p=l+1 ∨ p=l+3
  have adjData : ∀ i j : Fin 14, adj i j = true ↔ ∃ p l : Fin 7, inc p l ∧
      ((i = Fin.castAdd 7 p ∧ j = Fin.natAdd 7 l) ∨
       (j = Fin.castAdd 7 p ∧ i = Fin.natAdd 7 l)) := by decide +kernel
  have identity (x : Fin 14 → Bool) : target x ↔ ∃ p l : Fin 7, inc p l ∧
      x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
    constructor
    · rintro ⟨i,j,h,hi,hj⟩
      obtain ⟨p,l,pl,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (adjData i j).mp h
      · exact ⟨p,l,pl,hi,hj⟩
      · exact ⟨p,l,pl,hj,hi⟩
    · rintro ⟨p,l,pl,hp,hl⟩
      exact ⟨_,_,(adjData _ _).mpr ⟨p,l,pl,Or.inl ⟨rfl,rfl⟩⟩,hp,hl⟩
  let table : List ℕ := [573945371705473,2269461860090114,4538923588132868,2393091369861392,18296165611604000,1587760290848832,3663766027026912,6768946055808039,11549907977570382,18666416739814336,25901471711383817,36805067917039628,42364467165831464,56931619210045450,266352904]
  let row (r : Fin 60) (i : Fin 14) := (table.getD (r.val / 4) 0).testBit (14 * (r.val % 4) + i.val)
  let start (r : Fin 60) (i : Fin 14) : ℕ :=
    if r.val < 58 then if row r i then 0 else 2
    else if i.val = (if r.val=58 then 0 else 7) then 0
    else if i.val = (if r.val=58 then 7 else 0) then 1 else 2
  have boundary : ∀ r : Fin 60, r.val < 58 →
      (target (row r) ↔ r.val < 21) := by decide +kernel
  let mark (s : Bool) : Fin 14 := if s then 0 else 7
  let singleton (s : Bool) (i : Fin 14) := decide (i = mark s)
  have noSingleton : ∀ s : Bool, ¬ target (singleton s) := by decide +kernel
  intro C small ao distinct first correct passes
  have computes (x : Fin 14 → Bool) : C.eval (List.ofFn x) = true ↔ target x :=
    (correct x).trans (identity x).symm
  let w (x : Fin 14 → Bool) (i : ℕ) := (C.wires (List.ofFn x)).getD i false
  let step (u : List Bool) (g : Gate) := u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)]
  have sizeEq (gs : List Gate) (u : List Bool) : (gs.foldl step u).length = u.length + gs.length := by
    induction gs generalizing u with
    | nil => simp
    | cons g gs ih =>
      simp only [List.foldl_cons,ih,step,List.length_append,List.length_cons,List.length_nil]; omega
  have keep (gs : List Gate) (u : List Bool) (i : ℕ) (hi : i < u.length) :
      (gs.foldl step u).getD i false = u.getD i false := by
    induction gs generalizing u with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have raw (x : Fin 14 → Bool) (i : Fin 14) : w x i.val = x i := by
    change (C.gates.foldl step (List.ofFn x)).getD i.val false = _
    rw [keep _ _ _ (by simpa only [List.length_ofFn] using i.isLt),
      List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt),List.getElem_ofFn]
  have ops (j : ℕ) (hj : j < C.size) : (gateAt C j).op = .and ∨ (gateAt C j).op = .or := by
    rw [show gateAt C j = C.gates[j] from List.getD_eq_getElem _ _ hj]
    exact ao.1 _ (List.getElem_mem hj)
  have args (j : ℕ) (hj : j < C.size) : (gateAt C j).inputs = [opnd C j 0,opnd C j 1] := by
    have hgate : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
    have length := ao.2.2 (gateAt C j) (hgate ▸ List.getElem_mem hj)
    obtain ⟨a,b,hab⟩ := List.length_eq_two.mp length
    change (gateAt C j).inputs = [(gateAt C j).inputs.getD 0 0,(gateAt C j).inputs.getD 1 0]
    rw [hab]
    rfl
  have earlier (j : ℕ) (hj : j < C.size) (k : Fin 2) : opnd C j k < 14+j := by
    apply ao.2.1 j hj
    rw [args j hj]
    fin_cases k <;> simp
  have gateValue (j : ℕ) (hj : j < C.size) (x : Fin 14 → Bool) :
      w x (14+j) = (gateAt C j).op.eval [w x (opnd C j 0),w x (opnd C j 1)] := by
    let u := (C.gates.take j).foldl step (List.ofFn x)
    have len : u.length = 14+j := by rw [show u = _ from rfl,sizeEq,List.length_ofFn,List.length_take_of_le hj.le]
    have h : j < C.gates.length := hj
    have gEq : gateAt C j = C.gates[j]'h := List.getD_eq_getElem _ _ h
    have split : C.gates.take j ++ gateAt C j :: C.gates.drop (j+1) = C.gates := by
      rw [gEq,← List.drop_eq_getElem_cons h,List.take_append_drop]
    have full : C.wires (List.ofFn x) = (C.gates.drop (j+1)).foldl step (step u (gateAt C j)) := by
      calc
        _ = (C.gates.take j ++ gateAt C j :: C.gates.drop (j+1)).foldl step (List.ofFn x) :=
          congrArg (fun gs : List Gate => gs.foldl step (List.ofFn x)) split.symm
        _ = _ := by rw [List.foldl_append,List.foldl_cons]
    have tail (i : ℕ) (hi : i < 14+j) : w x i = u.getD i false := by
      change (C.wires (List.ofFn x)).getD i false = _
      rw [full]
      rw [keep _ _ _ (by simp [step,len]; omega)]
      exact List.getD_append _ _ _ _ (by omega)
    rw [tail _ (earlier j hj 0),tail _ (earlier j hj 1)]
    change (C.wires (List.ofFn x)).getD (14+j) false = _
    rw [full]
    rw [keep _ _ _ (by simp [step,len])]
    change (u ++ [_]).getD (14+j) false = _
    rw [List.getD_append_right _ _ _ _ (by omega),len,Nat.sub_self]
    change (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => u.getD i false) = _
    rw [args j hj]
    rfl
  have nonempty : 0 < C.size := by
    by_contra! empty
    have no : C.gates = [] := List.length_eq_zero_iff.mp (show C.gates.length = 0 by
      change C.gates.length ≤ 0 at empty; omega)
    change (C.gates.getD 0 ⟨GateOp.or,[]⟩).op = GateOp.and at first
    rw [no] at first
    exact GateOp.noConfusion first
  have outThere : C.output < 14+C.size := by
    by_contra! outside
    let x : Fin 14 → Bool := fun _ => true
    have yes := (correct x).mpr ⟨0,0,Or.inl rfl,rfl,rfl⟩
    change (C.gates.foldl step (List.ofFn x)).getD C.output false = true at yes
    rw [List.getD_eq_default _ _ (by rw [sizeEq,List.length_ofFn]; exact outside)] at yes
    exact Bool.noConfusion yes
  let a : Fin 14 := ⟨opnd C 0 0,by simpa using earlier 0 nonempty 0⟩
  let b : Fin 14 := ⟨opnd C 0 1,by simpa using earlier 0 nonempty 1⟩
  have neq : a ≠ b := fun eq => distinct 0 nonempty (congrArg Fin.val eq)
  obtain ⟨π,flag,preserves,representative⟩ := geometry a b neq
  have permutes (x : Fin 14 → Bool) : target (x ∘ π) ↔ target x := by
    constructor
    · rintro ⟨i,j,h,hi,hj⟩
      exact ⟨π i,π j,(preserves i j).trans h,hi,hj⟩
    · rintro ⟨i,j,h,hi,hj⟩
      refine ⟨π.symm i,π.symm j,?_,by simpa using hi,by simpa using hj⟩
      have eq := preserves (π.symm i) (π.symm j)
      rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply] at eq
      exact eq.symm.trans h
  let ren (i : ℕ) := if h : i < 14 then (π ⟨i,h⟩).val else i
  have renSmall {i t : ℕ} (h : i < 14+t) : ren i < 14+t := by
    unfold ren
    split
    · next h₁ => have := (π ⟨i,h₁⟩).isLt; omega
    · exact h
  have renInj : Function.Injective ren := by
    intro i j eq
    by_cases hi : i < 14 <;> by_cases hj : j < 14
    · simp only [ren,dite_eq_left hi,dite_eq_left hj] at eq
      exact congrArg Fin.val (π.injective (Fin.ext eq))
    · simp only [ren,dite_eq_left hi,dite_eq_right hj] at eq
      have := (π ⟨i,hi⟩).isLt; omega
    · simp only [ren,dite_eq_right hi,dite_eq_left hj] at eq
      have := (π ⟨j,hj⟩).isLt; omega
    · simpa only [ren,dite_eq_right hi,dite_eq_right hj] using eq
  let index (i : ℕ) : Fin 41 := ⟨min 40 (ren i),by omega⟩
  have indexEq {i : ℕ} (hi : i < 14+C.size) : (index i).val = ren i := by
    have := renSmall hi
    exact Nat.min_eq_right (by omega)
  let Code := Fin 41 × Fin 41 × Bool
  let encode (g : Gate) : Code := (index (g.inputs.getD 0 0),index (g.inputs.getD 1 0),g.op.eval [])
  let filler : Code := (0,1,false)
  let cells := C.gates.map encode ++ List.replicate (27-C.size) filler
  have len : cells.length = 27 := by
    change (C.gates.map encode ++ List.replicate (27-C.size) filler).length = 27
    simp only [List.length_append,List.length_map,List.length_replicate]
    change C.size+(27-C.size) = 27; omega
  let P : List.Vector Code 27 := ⟨cells,len⟩
  have real (j : Fin 27) (hj : j.val < C.size) : P.get j = encode (gateAt C j.val) := by
    have h : j.val < C.gates.length := hj
    change (C.gates.map encode ++ List.replicate (27-C.size) filler)[j.val]'(by change j.val < cells.length; rw [len]; exact j.isLt) = _
    rw [List.getElem_append_left (by simpa only [List.length_map] using h),List.getElem_map]
    exact congrArg encode (List.getD_eq_getElem C.gates ⟨GateOp.or,[]⟩ h).symm
  have extra (j : Fin 27) (hj : C.size ≤ j.val) : P.get j = filler := by
    have h : C.gates.length ≤ j.val := hj
    change (C.gates.map encode ++ List.replicate (27-C.size) filler)[j.val]'(by change j.val < cells.length; rw [len]; exact j.isLt) = _
    rw [List.getElem_append_right (by simpa only [List.length_map] using h)]
    simp only [List.getElem_replicate]
  have pinValid {j : ℕ} (hj : j < C.size) (k : Fin 2) :
      (index (opnd C j k)).val = ren (opnd C j k) := by
    have e := earlier j hj k
    exact indexEq (by omega)
  have legal (j : Fin 27) : (P.get j).1.val < 14+j.val ∧ (P.get j).2.1.val < 14+j.val ∧
      (P.get j).1 ≠ (P.get j).2.1 := by
    by_cases hj : j.val < C.size
    · rw [real j hj]
      change (index (opnd C j.val 0)).val < _ ∧ (index (opnd C j.val 1)).val < _ ∧
        index (opnd C j.val 0) ≠ index (opnd C j.val 1)
      refine ⟨(pinValid hj 0).trans_lt (renSmall (earlier _ hj 0)),
        (pinValid hj 1).trans_lt (renSmall (earlier _ hj 1)),?_⟩
      intro eq
      have v := congrArg Fin.val eq
      rw [pinValid hj 0,pinValid hj 1] at v
      exact distinct _ hj (renInj v)
    · rw [extra _ (by omega)]
      change 0 < 14+j.val ∧ 1 < 14+j.val ∧ (0 : Fin 41) ≠ 1
      exact ⟨by omega,by omega,by decide⟩
  have firstAnd : (P.get 0).2.2 = true := by
    rw [real _ nonempty]
    change (gateAt C 0).op.eval [] = true
    rw [first];rfl
  have shape : 14*min (P.get 0).1.val (P.get 0).2.1.val +
      max (P.get 0).1.val (P.get 0).2.1.val ∈ ([1,2,7,8,11,16,17,22,23,25,32,34,36,38] : List ℕ) := by
    rw [real _ nonempty]
    change 14*min (index (opnd C 0 0)).val (index (opnd C 0 1)).val +
      max (index (opnd C 0 0)).val (index (opnd C 0 1)).val ∈ _
    rw [pinValid nonempty 0,pinValid nonempty 1]
    simpa only [ren,dite_eq_left (show opnd C 0 0 < 14 from a.isLt),
        dite_eq_left (show opnd C 0 1 < 14 from b.isLt)] using representative
  let combine (tag : Bool) (u v : ℕ) := cond tag (min 2 (u+v)) (min u v)
  let run (u : List ℕ) (g : Code) := u ++ [combine g.2.2 (u.getD g.1.val 2) (u.getD g.2.1.val 2)]
  have runLen (gs : List Code) (u : List ℕ) : (gs.foldl run u).length = u.length+gs.length := by
    induction gs generalizing u with
    | nil => simp
    | cons g gs ih =>
      simp only [List.foldl_cons,ih,run,List.length_append,List.length_cons,List.length_nil];omega
  have runKeep (gs : List Code) (u : List ℕ) (i : ℕ) (hi : i < u.length) :
      (gs.foldl run u).getD i 2 = u.getD i 2 := by
    induction gs generalizing u with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih _ (by simp [run];omega)]
      exact List.getD_append _ _ _ _ hi
  have simulation (x : Fin 14 → ℕ) (v : ℕ → ℕ)
      (src : ∀ i : Fin 14, v i.val = x (π i))
      (gates : ∀ j < C.size, v (14+j) = combine ((gateAt C j).op.eval []) (v (opnd C j 0)) (v (opnd C j 1))) :
      (P.toList.foldl run (List.ofFn x)).getD (index C.output).val 2 = v C.output := by
    let bank (j : ℕ) := ((C.gates.take j).map encode).foldl run (List.ofFn x)
    have width {j : ℕ} (hj : j ≤ C.size) : (bank j).length = 14+j := by
      simp only [bank,runLen,List.length_ofFn,List.length_map,List.length_take_of_le hj]
    have agrees (j : ℕ) (hj : j ≤ C.size) : ∀ i < 14+j, (bank j).getD (ren i) 2 = v i := by
      induction j with
      | zero =>
        intro i h
        have smallI : i < 14 := by omega
        simp only [ren,dite_eq_left smallI,bank,List.take_zero,List.map_nil,List.foldl_nil]
        rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using (π ⟨i,smallI⟩).isLt),
          List.getElem_ofFn]
        exact (src ⟨i,smallI⟩).symm
      | succ j ih =>
        intro i hi
        have jj : j < C.size := by omega
        have snoc : bank (j+1) = run (bank j) (encode (gateAt C j)) := by
          rw [show gateAt C j = C.gates[j] from List.getD_eq_getElem _ _ jj]
          simp only [bank,List.take_succ_eq_append_getElem jj,List.map_append,List.map_cons,List.map_nil,
            List.foldl_append,List.foldl_cons,List.foldl_nil]
        rw [snoc]
        by_cases before : i < 14+j
        · change (bank j ++ [_]).getD (ren i) 2 = _
          rw [List.getD_append _ _ _ _ (by rw [width jj.le]; exact renSmall before)]
          exact ih jj.le i before
        · have eq : i = 14+j := by omega
          subst i
          have rr : ren (14+j) = 14+j := by simp [ren]
          rw [rr,gates j jj]
          change (bank j ++ [combine _ ((bank j).getD (index (opnd C j 0)).val 2)
            ((bank j).getD (index (opnd C j 1)).val 2)]).getD (14+j) 2 = _
          rw [List.getD_append_right _ _ _ _ (by rw [width jj.le]),width jj.le,Nat.sub_self]
          change combine _ ((bank j).getD (index (opnd C j 0)).val 2)
            ((bank j).getD (index (opnd C j 1)).val 2) = _
          rw [pinValid jj 0,pinValid jj 1,ih jj.le _ (earlier j jj 0),ih jj.le _ (earlier j jj 1)]
    have main := agrees C.size le_rfl C.output outThere
    have whole : bank C.size = (C.gates.map encode).foldl run (List.ofFn x) := by
      change ((C.gates.take C.gates.length).map encode).foldl run (List.ofFn x) = _
      rw [List.take_length]
    change ((C.gates.map encode ++ List.replicate (27-C.size) filler).foldl run _).getD _ 2 = _
    rw [List.foldl_append,← whole,indexEq outThere,
      runKeep _ _ _ (by rw [width le_rfl];exact renSmall outThere)]
    exact main
  let ordinary (u : Bool) : ℕ := if u then 0 else 2
  let cost (u d : Bool) : ℕ := if u then 0 else if d then 1 else 2
  have andValue (u v : Bool) : GateOp.and.eval [u,v] = (u && v) := by cases u <;> cases v <;> rfl
  have orValue (u v : Bool) : GateOp.or.eval [u,v] = (u || v) := by cases u <;> cases v <;> rfl
  have plainAnd (u v : Bool) : ordinary (u && v) = combine true (ordinary u) (ordinary v) := by
    cases u <;> cases v <;> rfl
  have plainOr (u v : Bool) : ordinary (u || v) = combine false (ordinary u) (ordinary v) := by
    cases u <;> cases v <;> rfl
  have taggedAnd : ∀ u du v dv : Bool,
      cost (u && v) ((u && dv) || (du && v)) = combine true (cost u du) (cost v dv) := by decide +kernel
  have taggedOr : ∀ u du v dv : Bool,
      cost (u || v) (du || dv) = combine false (cost u du) (cost v dv) := by decide +kernel
  obtain ⟨r,wrong⟩ := excluded P (index C.output) legal firstAnd shape
  apply wrong
  change (P.toList.foldl run (List.ofFn (start r))).getD (index C.output).val 2 = _
  by_cases plain : r.val < 58
  · let x := row r ∘ π
    have src (i : Fin 14) : ordinary (w x i.val) = start r (π i) := by
      rw [raw]
      simp only [start,ite_eq_left plain,x,Function.comp_apply,ordinary]
    have rule (j : ℕ) (hj : j < C.size) : ordinary (w x (14+j)) =
        combine ((gateAt C j).op.eval []) (ordinary (w x (opnd C j 0))) (ordinary (w x (opnd C j 1))) := by
      rw [gateValue j hj]
      rcases ops j hj with h | h
      · rw [h,andValue]
        exact plainAnd _ _
      · rw [h,orValue]
        exact plainOr _ _
    rw [simulation (start r) (fun i => ordinary (w x i)) src rule]
    have flagValue : w x C.output = true ↔ r.val < 21 :=
      (computes x).trans ((permutes (row r)).trans (boundary r plain))
    by_cases good : r.val < 21
    · simp only [ordinary,flagValue.mpr good,ite_true,ite_eq_left good]
    · have zero : w x C.output = false := Bool.eq_false_iff.mpr (fun h => good (flagValue.mp h))
      simp only [ordinary,zero,Bool.false_eq_true,ite_false,ite_eq_right good]
  · let t : Bool := decide (r.val=58)
    have rowTag : ∀ (q : Fin 60) (i : Fin 14), 58 ≤ q.val →
        start q i = cost (singleton (decide (q.val=58)) i) (singleton (!(decide (q.val=58))) i) := by decide +kernel
    have orient : ∃ s : Bool, π (mark s) = mark t ∧ π (mark (!s)) = mark (!t) := by
      rcases flag with ⟨p,l⟩ | ⟨p,l⟩
      · exact ⟨t,by cases t <;> simp [mark,p,l],by cases t <;> simp [mark,p,l]⟩
      · exact ⟨!t,by cases t <;> simp [mark,p,l],by cases t <;> simp [mark,p,l]⟩
    obtain ⟨s,mapped,mapped'⟩ := orient
    obtain ⟨d,hd,stepD,flat⟩ := passes s
    have data : ∀ (side : Bool) (i : Fin 14),
        decide (i.val = (if side then 7 else 0)) = singleton (!side) i := by decide +kernel
    have dirInput (i : Fin 14) : d i.val = singleton (!s) i := by
      exact (hd i.val i.isLt).trans (data s i)
    have changeMark (a b : Bool) (maps : π (mark a) = mark b) (i : Fin 14) :
        singleton b (π i) = singleton a i := by
      simp only [singleton,← maps,Equiv.apply_eq_iff_eq]
    let x := singleton s
    let val (i : ℕ) := cost (w x i) (d i)
    have src (i : Fin 14) : val i.val = start r (π i) := by
      rw [rowTag r (π i) (by omega)]
      change cost (w x i.val) (d i.val) = cost (singleton t (π i)) (singleton (!t) (π i))
      rw [raw,dirInput,changeMark s t mapped,changeMark (!s) (!t) mapped']
    have rule (j : ℕ) (hj : j < C.size) : val (14+j) =
        combine ((gateAt C j).op.eval []) (val (opnd C j 0)) (val (opnd C j 1)) := by
      unfold val
      rw [gateValue j hj]
      rcases ops j hj with h | h
      · rw [h,andValue,(stepD j hj).1 h]
        exact taggedAnd _ _ _ _
      · rw [h,orValue,(stepD j hj).2 h]
        exact taggedOr _ _ _ _
    have baseOff : w x C.output = false := Bool.eq_false_iff.mpr
      (fun on => noSingleton s ((computes x).mp on))
    rw [simulation (start r) val src rule]
    simp only [val,baseOff,flat,cost,Bool.false_eq_true,ite_false,ite_eq_right (by omega : ¬r.val < 21)]
