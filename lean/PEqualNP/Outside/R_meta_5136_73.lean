import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Defs.LratEncoding

-- The signed prerequisites and their translation come from Gan-Tu's checked R_meta_1665_41.
-- A satisfying assignment is decoded inside the proof. Both remaining premises are checked warehouse theorems.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_5136_73 :
  (∀ (b : ℕ) (op : Fin b → Bool) (left right : Fin b → ℕ × Bool)
    (out : ℕ × Bool) (w : (Fin 9 → Bool) → ℕ → Bool), b ≤ 10 →
    (∀ j, (left j).1 < 10 + j.val ∧ (right j).1 < 10 + j.val) → out.1 < 10 + b →
    (∀ x (i : Fin 9), w x i.val = x i) → (∀ x, w x 9 = false) →
    (∀ x j, let val := fun p : ℕ × Bool => Bool.xor (w x p.1) p.2
      w x (10 + j.val) = if op j then (val (left j) && val (right j))
        else (val (left j) || val (right j))) →
    ∃ x : Fin 9 → Bool, Bool.xor (w x out.1) out.2 ≠
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
  (∀ (b : ℕ) (op : Fin b → Bool) (left right : Fin b → ℕ × Bool)
    (out : ℕ × Bool) (paid : Finset ℕ) (w : (Fin 9 → Bool) → ℕ → Bool),
    paid.card ≤ 3 → b + paid.card ≤ 14 →
    (∀ j, (left j).1 < 10 + j.val ∧ (right j).1 < 10 + j.val) → out.1 < 10 + b →
    (let ok := fun p : ℕ × Bool => p.2 = true → p.1 = 0 ∨ p.1 = 9 ∨ p.1 ∈ paid
     ok out ∧ ∀ j, ok (left j) ∧ ok (right j)) →
    (∀ x (i : Fin 9), w x i.val = x i) → (∀ x, w x 9 = false) →
    (∀ x j, let val := fun p : ℕ × Bool => Bool.xor (w x p.1) p.2
      w x (10 + j.val) = if op j then (val (left j) && val (right j))
        else (val (left j) || val (right j))) →
    ∃ x : Fin 9 → Bool, Bool.xor (w x out.1) out.2 ≠
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
  ¬PEqualNP.Defs.LratEncoding.FormulaSat     (PEqualNP.Defs.LratEncoding.enc (11 : ℕ) (13 : ℕ) (fun (x1 : ℕ) => [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)].any fun (x2 : ℕ) => x1 &&& x2 == x2)       (have x1 : List ℕ :=         have x1 : List ℕ :=           have x1 : List ℕ := [(1744 : ℕ), (1800 : ℕ), (1824 : ℕ), (1856 : ℕ), (1938 : ℕ)];           (1648 : ℕ) :: (1674 : ℕ) :: (1696 : ℕ) :: (1736 : ℕ) :: x1;         have x2 : List ℕ := (1560 : ℕ) :: (1578 : ℕ) :: (1586 : ℕ) :: (1602 : ℕ) :: (1640 : ℕ) :: x1;         (1225 : ℕ) :: (1289 : ℕ) :: (1345 : ℕ) :: (1409 : ℕ) :: x2;       have x2 : List ℕ :=         have x2 : List ℕ := (804 : ℕ) :: (836 : ℕ) :: (1027 : ℕ) :: (1041 : ℕ) :: (1057 : ℕ) :: x1;         (524 : ℕ) :: (628 : ℕ) :: (644 : ℕ) :: (788 : ℕ) :: x2;       have x3 : List ℕ := (69 : ℕ) :: (133 : ℕ) :: (261 : ℕ) :: (325 : ℕ) :: (518 : ℕ) :: x2;       (7 : ℕ) :: (13 : ℕ) :: (21 : ℕ) :: (37 : ℕ) :: x3)) := by
  intro unrestricted few
  have decodeCNF : ∀ (n s : ℕ) (g : ℕ→Bool) (rows : List ℕ),
    PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc n s g rows) →
    ∃ C : Circuit, FanInTwo C ∧ C.size=s ∧
      (∀ x y : Fin n→Bool, (∀ i, x i=true → y i=true) → C.eval (List.ofFn x)=true → C.eval (List.ofFn y)=true) ∧
      ∀ r∈rows, C.eval (List.ofFn (fun i : Fin n => r.testBit i.val))=g r := by
    clear unrestricted few
    have evalAnd (l : List Bool) : GateOp.and.eval l=l.all id := rfl
    have evalOr (l : List Bool) : GateOp.or.eval l=l.any id := rfl
    let wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
    have wiresFrom_append (gs rest : List Gate) (w : List Bool) :
        wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
      simp [wiresFrom, List.foldl_append]
    have wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
        ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
      induction gs with
      | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
      | cons g gs ih =>
        intro w
        obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
        change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
        rw [ht]; simp
    have wiresFrom_length (gs : List Gate) (w : List Bool) :
        (wiresFrom gs w).length = w.length + gs.length := by
      obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
      rw [ht]; simp [hl]
    have prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
        (wiresFrom gs w).getD i false = w.getD i false := by
      obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
      rw [ht, List.getD_append _ _ _ _ h]
    let val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
      (wiresFrom C.gates (List.ofFn x)).getD i false
    have val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
        val C x i.val = x i := by
      unfold val; rw [ prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
      simp
    have val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
        (hi : n + C.gates.length ≤ i) : val C x i = false := by
      unfold val; rw [ List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]
    let operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
      if i < j then val C x i else false
    have val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
        (hp : C.gates[p]? = some g) :
        val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
      obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
      have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
        conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
        rw [List.take_succ_eq_append_getElem hb, heq]
      let w := wiresFrom (C.gates.take p) (List.ofFn x)
      have hw : w.length = n+p := by
        simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
      have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
        by_cases hi : i < n+p
        · have hv : val C x i = w.getD i false := by
            unfold val
            conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
            exact prefix_val _ w i (hw.symm ▸ hi)
          simp only [operand, ite_eq_left hi, hv]
        · unfold operand; rw [ ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
      have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
        List.map_congr_left fun i _ => hread i
      unfold val
      conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
      change (wiresFrom (C.gates.drop (p+1))
        (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
      rw [prefix_val _ _ _ (by simp [hw]), ← hw, he]
      simp [hw]
    let semantic (n s : ℕ) (g : ℕ→Bool) (rows : List ℕ) : List (List ℕ) :=
      fOp n s ++ fSrcAlo n s ++ fSrcEq n s rows ++ fGate n s rows ++ fOutAlo n s ++ fOutEq n s g rows
    have semantic_of_enc {n s : ℕ} {g : ℕ→Bool} {rows : List ℕ} :
        FormulaSat (enc n s g rows) → FormulaSat (semantic n s g rows) := by
      rintro ⟨A,ok⟩
      refine ⟨A,fun c hc => ok c ?_⟩
      simp only [semantic,List.mem_append] at hc
      unfold enc; simp only [List.mem_append]
      tauto
    have sat_cons (A : ℕ→Bool) (v : ℕ) (c : List ℕ) :
        ClauseSat A (v::c) ↔ litVal A v=true ∨ ClauseSat A c := by unfold ClauseSat; simp
    have sat_nil (A : ℕ→Bool) : ¬ClauseSat A [] := by unfold ClauseSat; simp
    have lit_pos (A : ℕ→Bool) (v : ℕ) : litVal A (P v)=A (v+1) := by
      unfold litVal P
      rw [show (2*v+2)/2=v+1 by omega,show (2*v+2)%2=0 by omega]
      cases A (v+1) <;> rfl
    have lit_neg (A : ℕ→Bool) (v : ℕ) : litVal A (Q v)=!(A (v+1)) := by
      unfold litVal Q
      rw [show (2*v+3)/2=v+1 by omega,show (2*v+3)%2=1 by omega]
      cases A (v+1) <;> rfl
    have lit_label (A : ℕ→Bool) (v : ℕ) (b : Bool) : litVal A (L v b)=true ↔ A (v+1)=b := by
      cases b <;> unfold L <;> simp [lit_pos,lit_neg]
    let get (A : ℕ→Bool) (n s k j a : ℕ) := A (ix n s k j a + 1)
    let readVal (A : ℕ→Bool) (n s j r k : ℕ) := if k<n then r.testBit k else if k<n+j then get A n s 3 (k-n) r else false
    have source_value (n s e j k r : ℕ) (A : ℕ→Bool) (chosen : get A n s e j k=true)
        (clauses : ∀ c ∈ srcEq n s e j k r, ClauseSat A c) :
        get A n s (e+3) j r = readVal A n s j r k := by
      unfold get at chosen ⊢
      unfold readVal srcEq at *
      by_cases raw : k<n
      · simp only [ite_eq_left raw,List.mem_singleton,forall_eq] at clauses ⊢
        simpa only [sat_cons,lit_pos,lit_neg,chosen,Bool.not_true,reduceCtorEq,false_or,lit_label,sat_nil,or_false] using clauses
      · by_cases prev : k<n+j
        · simp only [ite_eq_right raw,ite_eq_left prev,List.mem_cons,List.not_mem_nil,or_false] at clauses ⊢
          have a := clauses _ (Or.inl rfl)
          have b := clauses _ (Or.inr rfl)
          simp only [sat_cons,lit_pos,lit_neg,chosen,Bool.not_true,reduceCtorEq,false_or,sat_nil,or_false] at a b
          unfold get
          cases h1 : A (ix n s (e+3) j r+1) <;> cases h2 : A (ix n s 3 (k-n) r+1) <;> simp_all
        · simp only [ite_eq_right raw,ite_eq_right prev,List.mem_singleton,forall_eq] at clauses ⊢
          simpa only [sat_cons,lit_pos,lit_neg,chosen,Bool.not_true,reduceCtorEq,false_or,sat_nil,or_false,
            Bool.not_eq_true'] using clauses
    have output_value (n s r k : ℕ) (g : ℕ→Bool) (A : ℕ→Bool) (chosen : get A n s 6 0 k=true)
        (clauses : ∀ c ∈ outEq n s g k r, ClauseSat A c) : readVal A n s s r k=g r := by
      unfold get at chosen
      unfold outEq at clauses
      unfold readVal
      by_cases raw : k<n
      · simp only [ite_eq_left raw] at clauses ⊢
        by_contra bad
        simp only [ite_eq_right bad,List.mem_singleton,forall_eq,sat_cons,lit_neg,chosen,Bool.not_true,
          reduceCtorEq,sat_nil,false_or] at clauses
      · by_cases prev : k<n+s
        · simp only [ite_eq_right raw,ite_eq_left prev,List.mem_singleton,forall_eq] at clauses ⊢
          simpa only [get,sat_cons,lit_neg,chosen,Bool.not_true,reduceCtorEq,false_or,lit_label,sat_nil,or_false] using clauses
        · simp only [ite_eq_right raw,ite_eq_right prev] at clauses ⊢
          cases val : g r with
          | false => rfl
          | true => simp only [val,ite_true,List.mem_singleton,forall_eq,sat_cons,lit_neg,chosen,Bool.not_true,
              reduceCtorEq,sat_nil,false_or] at clauses
    have clauses_compute (n s j r : ℕ) (A : ℕ→Bool) (op : Fin 3)
        (pick : get A n s 0 j op.val=true) (clauses : ∀ c ∈ gateCl n s j r, ClauseSat A c) :
        get A n s 3 j r = if op.val=0 then (get A n s 4 j r && get A n s 5 j r)
          else if op.val=1 then (get A n s 4 j r || get A n s 5 j r) else true := by
      let a := get A n s 4 j r
      let b := get A n s 5 j r
      let v := get A n s 3 j r
      have hl (i : Fin 7) : ClauseSat A ((gateCl n s j r).get ⟨i.val,i.isLt⟩) :=
        clauses _ (List.get_mem _ _)
      have h0 := hl 0; have h1 := hl 1; have h2 := hl 2; have h3 := hl 3
      have h4 := hl 4; have h5 := hl 5; have h6 := hl 6
      unfold gateCl at h0 h1 h2 h3 h4 h5 h6
      unfold get at pick ⊢
      fin_cases op <;>
        cases va : A (ix n s 4 j r + 1) <;> cases vb : A (ix n s 5 j r + 1) <;>
        cases vo : A (ix n s 3 j r + 1) <;> simp_all [sat_cons,sat_nil,lit_pos,lit_neg]
    have choose_positive (A : ℕ→Bool) (ks : List ℕ) (v : ℕ→ℕ)
        (h : ClauseSat A (ks.map fun k => P (v k))) : ∃ k ∈ ks, A (v k+1)=true := by
      obtain ⟨q,hq,y⟩ := h
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hq
      exact ⟨k,hk,(lit_pos A _).symm.trans y⟩
    let decodedGate {s : ℕ} (op : Fin s→Fin 3) (a b : Fin s→ℕ) (j : Fin s) : Gate :=
      if (op j).val=0 then ⟨.and,[a j,b j]⟩ else if (op j).val=1 then ⟨.or,[a j,b j]⟩ else ⟨.and,[]⟩
    have decode (n s : ℕ) (g : ℕ→Bool) (rows : List ℕ) (sat : FormulaSat (semantic n s g rows)) :
        ∃ C : Circuit, Monotone2 C ∧ C.size=s ∧
          ∀ r ∈ rows, C.eval (List.ofFn (fun i : Fin n => r.testBit i.val))=g r := by
      classical
      obtain ⟨A,valid⟩ := sat
      have ops (j : Fin s) : ∃ op : Fin 3, get A n s 0 j.val op.val=true := by
        have mem : [P (ix n s 0 j.val 0),P (ix n s 0 j.val 1),P (ix n s 0 j.val 2)] ∈ fOp n s :=
          List.mem_map.mpr ⟨j.val,List.mem_range.mpr j.isLt,rfl⟩
        have c := valid _ (by simp only [semantic,List.mem_append];tauto)
        simp only [sat_cons,lit_pos,sat_nil,or_false] at c
        rcases c with h|h|h
        · exact ⟨0,h⟩
        · exact ⟨1,h⟩
        · exact ⟨2,h⟩
      choose op opTrue using ops
      have src (e : ℕ) (he : e ∈ ([1,2] : List ℕ)) (j : Fin s) :
          ∃ k : ℕ, k ≤ n+j.val ∧ get A n s e j.val k=true := by
        have mem : ((List.range (n+j.val+1)).map fun k => P (ix n s e j.val k)) ∈ fSrcAlo n s :=
          List.mem_flatMap.mpr ⟨e,he,List.mem_map.mpr ⟨j.val,List.mem_range.mpr j.isLt,rfl⟩⟩
        obtain ⟨k,inR,h⟩ := choose_positive A _ _ (valid _ (by simp only [semantic,List.mem_append];tauto))
        exact ⟨k,by have := List.mem_range.mp inR;omega,h⟩
      choose a aBound aTrue using src 1 (by decide)
      choose b bBound bTrue using src 2 (by decide)
      have outMem : ((List.range (n+s+1)).map fun k => P (ix n s 6 0 k)) ∈ fOutAlo n s := List.mem_singleton.mpr rfl
      obtain ⟨out,outRange,outTrue⟩ := choose_positive A _ _ (valid _ (by simp only [semantic,List.mem_append];tauto))
      let gs := List.ofFn (decodedGate op a b)
      let C : Circuit := ⟨gs,out⟩
      have len : C.gates.length=s := List.length_ofFn
      refine ⟨C,?_,len,?_⟩
      · intro k hk
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hk
        unfold decodedGate
        split
        · exact ⟨Or.inl rfl,show (2:ℕ) ≤ 2 from le_rfl⟩
        · split
          · exact ⟨Or.inr rfl,show (2:ℕ) ≤ 2 from le_rfl⟩
          · exact ⟨Or.inl rfl,Nat.zero_le 2⟩
      intro r hr
      have rowSource (e : ℕ) (he : e ∈ ([1,2] : List ℕ)) (j : Fin s) (k : ℕ) (hk : k ≤ n+j.val)
          (selected : get A n s e j.val k=true) : get A n s (e+3) j.val r = readVal A n s j.val r k := by
        apply source_value _ _ _ _ _ _ _ selected
        intro c hc
        have inside : c ∈ fSrcEq n s rows := List.mem_flatMap.mpr ⟨e,he,List.mem_flatMap.mpr
          ⟨j.val,List.mem_range.mpr j.isLt,List.mem_flatMap.mpr ⟨r,hr,List.mem_flatMap.mpr
            ⟨k,List.mem_range.mpr (by omega),hc⟩⟩⟩⟩
        apply valid c; simp only [semantic,List.mem_append];tauto
      have gateResult (j : Fin s) : get A n s 3 j.val r =
          if (op j).val=0 then (readVal A n s j.val r (a j) && readVal A n s j.val r (b j))
          else if (op j).val=1 then (readVal A n s j.val r (a j) || readVal A n s j.val r (b j)) else true := by
        have h := clauses_compute n s j.val r A (op j) (opTrue j) (by
          intro c hc
          have inside : c ∈ fGate n s rows := List.mem_flatMap.mpr ⟨j.val,List.mem_range.mpr j.isLt,List.mem_flatMap.mpr ⟨r,hr,hc⟩⟩
          apply valid c; simp only [semantic,List.mem_append];tauto)
        have l := rowSource 1 (by decide) j (a j) (aBound j) (aTrue j)
        have q := rowSource 2 (by decide) j (b j) (bBound j) (bTrue j)
        change get A n s 4 j.val r = _ at l
        change get A n s 5 j.val r = _ at q
        rwa [l,q] at h
      have finalRow : readVal A n s s r out=g r := by
        apply output_value _ _ _ _ _ _ outTrue
        intro c hc
        have inside : c ∈ fOutEq n s g rows := List.mem_flatMap.mpr ⟨r,hr,List.mem_flatMap.mpr ⟨out,outRange,hc⟩⟩
        apply valid c; simp only [semantic,List.mem_append];tauto
      let x := fun i : Fin n => r.testBit i.val
      have allWires (i : ℕ) (h : i<n+s) : val C x i = if i<n then r.testBit i else get A n s 3 (i-n) r := by
        induction i using Nat.strong_induction_on with
        | ind i ih =>
          by_cases raw : i<n
          · rw [ite_eq_left raw];exact val_input C x ⟨i,raw⟩
          · let j : Fin s := ⟨i-n,by omega⟩
            have position : i=n+j.val := by dsimp [j];omega
            have found : C.gates[j.val]?=some (decodedGate op a b j) := by
              change (List.ofFn (decodedGate op a b))[j.val]?=_
              simp [List.getElem?_ofFn,j.isLt]
            have pin (z : ℕ) : operand C x (n+j.val) z=readVal A n s j.val r z := by
              by_cases early : z<n+j.val
              · change (if z<n+j.val then val C x z else false)=_
                rw [ite_eq_left early,ih z (by omega) (by omega)]
                simp only [readVal,ite_eq_left early]
              · simp [operand,readVal,early,show ¬z<n by omega]
            have wg := val_gate C x found
            rw [ite_eq_right raw,position,Nat.add_sub_cancel_left]
            change val C x (n+j.val)=get A n s 3 j.val r
            rw [wg,gateResult j]
            by_cases isAnd : (op j).val=0
            · simp only [decodedGate,ite_eq_left isAnd,List.map_cons,List.map_nil,evalAnd,evalOr,List.all_cons,List.all_nil,id_eq,Bool.and_true,pin]
            · by_cases isOr : (op j).val=1
              · simp only [decodedGate,ite_eq_right isAnd,ite_eq_left isOr,List.map_cons,List.map_nil,evalAnd,evalOr,List.any_cons,List.any_nil,id_eq,Bool.or_false,pin]
              · simp only [decodedGate,ite_eq_right isAnd,ite_eq_right isOr,List.map_nil,evalAnd,evalOr,List.all_nil]
      change val C x out=g r
      rw [←finalRow]
      by_cases available : out<n+s
      · rw [allWires out available]
        simp only [readVal,ite_eq_left available]
      · rw [val_beyond C x (by omega)]
        simp [readVal,available,show ¬out<n by omega]
    have acts_mono {n : ℕ} {C : Circuit} (hC : Monotone2 C) {x y : Fin n → Bool}
        (hxy : ∀ i, x i = true → y i = true) :
        ∀ j, val C x j = true → val C y j = true := by
      intro j
      induction j using Nat.strong_induction_on with
      | ind j ih =>
        intro hj
        by_cases hin : j < n
        · let i : Fin n := ⟨j, hin⟩
          simpa only [← val_input C x i, ← val_input C y i] using hxy i (by
            simpa only [← val_input C x i] using hj)
        by_cases hgt : n + C.gates.length ≤ j
        · rw [val_beyond C x hgt] at hj
          contradiction
        obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
        let g := C.gates[p]
        have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
        have hgate := (hC g (List.mem_of_getElem? hg)).1
        have hm (a : ℕ) : operand C x (n+p) a = true → operand C y (n+p) a = true := by
          by_cases ha : a < n+p
          · simp only [operand, ite_eq_left ha]
            exact ih a ha
          · simp [operand, ha]
        rw [val_gate C x hg] at hj
        rw [val_gate C y hg]
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgate
        rcases hgate with h | h
        · simp only [h, evalAnd,evalOr, List.all_map, Function.comp_apply, id, List.all_eq_true] at hj ⊢
          exact fun a ha => hm a (hj a ha)
        · simp only [h, evalAnd,evalOr, List.any_map, Function.comp_apply, id, List.any_eq_true] at hj ⊢
          obtain ⟨a, ha, he⟩ := hj
          exact ⟨a, ha, hm a he⟩
    intro n s g rows sat
    obtain ⟨C,mono,sz,fit⟩ := decode n s g rows (semantic_of_enc sat)
    refine ⟨C,?_,sz,?_,fit⟩
    · intro gate mem
      obtain ⟨op,bound⟩ := mono gate mem
      refine ⟨?_,bound⟩
      rcases op with eq|eq
      · exact Or.inl eq
      · exact Or.inr (Or.inl eq)
    · intro x y relation on
      exact acts_mono mono relation C.output on
  have firstNot : ∀ C : Circuit, FanInTwo C →
    (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 0)) →
    circuitFun 9 C = (fun x : Fin 9 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
    intro C fan first correct
    classical
    by_contra insufficient
    have small : C.size ≤ 15 := by omega
    let target := fun x : Fin 9 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
    let Pin := ℕ × Bool
    let Node := Bool × Pin × Pin
    let neg := fun (p : Pin) => (p.1,!p.2)
    let c0 : Pin := (9,false)
    let takePin := fun (w : List Bool) (p : Pin) => Bool.xor (w.getD p.1 false) p.2
    let bindGate := fun (w : List Bool) (g : Node) =>
      w ++ [if g.1 then (takePin w g.2.1 && takePin w g.2.2)
            else (takePin w g.2.1 || takePin w g.2.2)]
    let run := fun (P : List Node) (x : Fin 9 → Bool) => P.foldl bindGate (List.ofFn x ++ [false])
    let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    let seed := fun x : Fin 9 → Bool => List.ofFn x ++ [!(x 0)]
    let old := fun (gs : List Gate) (x : Fin 9 → Bool) => gs.foldl step (seed x)
    let allowed := fun (S : Finset ℕ) (p : Pin) => p.2 = true → p.1 = 0 ∨ p.1 = 9 ∨ p.1 ∈ S
    let ordered := fun (P : List Node) => ∀ j : Fin P.length,
      (P.get j).2.1.1 < 10 + j.val ∧ (P.get j).2.2.1 < 10 + j.val
    let state := fun (gs : List Gate) (P : List Node) (S : Finset ℕ) (M : List Pin) =>
      P.length + S.card ≤ gs.length ∧ ordered P ∧
      (∀ g ∈ P, allowed S g.2.1 ∧ allowed S g.2.2) ∧
      (∀ p ∈ M, p.1 < 10 + P.length ∧ allowed S p) ∧
      ∀ x, old gs x = M.map (takePin (run P x))
    have more {α : Type} (op : List Bool → α → Bool) (gs : List α) (w : List Bool) :
        ∃ t, gs.foldl (fun v g => v ++ [op v g]) w = w ++ t ∧ t.length = gs.length := by
      induction gs generalizing w with
      | nil => exact ⟨[],by simp,rfl⟩
      | cons g gs ih =>
        obtain ⟨t,he,hl⟩ := ih (w ++ [op w g])
        exact ⟨op w g :: t, by simp only [List.foldl_cons, he, List.append_assoc,
          List.cons_append, List.nil_append], by simp [hl]⟩
    have shape (P : List Node) (x : Fin 9 → Bool) :
        ∃ t, run P x = (List.ofFn x ++ [false]) ++ t ∧ t.length = P.length := by
      exact more (fun w (g : Node) => if g.1 then (takePin w g.2.1 && takePin w g.2.2)
        else (takePin w g.2.1 || takePin w g.2.2)) P _
    have width (P : List Node) (x : Fin 9 → Bool) : (run P x).length = 10 + P.length := by
      obtain ⟨t,he,hl⟩ := shape P x
      simp [he,hl]
      omega
    have constZero (P : List Node) (x : Fin 9 → Bool) : (run P x).getD 9 false = false := by
      obtain ⟨t,he,_⟩ := shape P x
      rw [he, List.getD_append _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
      simp
    have falsePin (P : List Node) (x : Fin 9 → Bool) : takePin (run P x) c0 = false := by
      change ((run P x).getD 9 false ^^ false) = false
      rw [constZero]
      rfl
    have complemented (w : List Bool) (p : Pin) : takePin w (neg p) = !(takePin w p) := by
      simp only [takePin,neg]
      cases w.getD p.1 false <;> cases p.2 <;> rfl
    have keepAllowed {S T : Finset ℕ} (h : S ⊆ T) {p : Pin} (a : allowed S p) : allowed T p := by
      intro on
      obtain z | k | mem := a on
      · exact Or.inl z
      · exact Or.inr (Or.inl k)
      · exact Or.inr (Or.inr (h mem))
    have getOK (P : List Node) (S : Finset ℕ) (M : List Pin)
        (hm : ∀ p ∈ M, p.1 < 10 + P.length ∧ allowed S p) (i : ℕ) :
        (M.getD i c0).1 < 10 + P.length ∧ allowed S (M.getD i c0) := by
      by_cases hi : i < M.length
      · rw [List.getD_eq_getElem _ _ hi]
        exact hm _ (List.getElem_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]
        exact ⟨by simp [c0]; omega, by simp [allowed,c0]⟩
    have longer {P : List Node} (hP : ordered P) (g : Node)
        (ha : g.2.1.1 < 10 + P.length) (hb : g.2.2.1 < 10 + P.length) :
        ordered (P ++ [g]) := by
      intro j
      change (P ++ [g])[j.val].2.1.1 < 10 + j.val ∧ (P ++ [g])[j.val].2.2.1 < 10 + j.val
      by_cases hi : j.val < P.length
      · rw [List.getElem_append_left hi]
        exact hP ⟨j.val,hi⟩
      · have eq : j.val = P.length := by have hj := j.isLt; simp at hj; omega
        simp only [eq]
        rw [List.getElem_append_right (Nat.le_refl P.length)]
        simp only [Nat.sub_self,List.getElem_cons_zero]
        exact ⟨ha,hb⟩
    have compile (gs : List Gate)
        (ok : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
        ∃ P S M, state gs P S M := by
      induction gs using List.reverseRecOn with
      | nil =>
        let m : List Pin := [(0,false),(1,false),(2,false),(3,false),(4,false),
          (5,false),(6,false),(7,false),(8,false),(0,true)]
        refine ⟨[],∅,m,by simp,fun j => Fin.elim0 j,by simp,?_,?_⟩
        · simp [m,allowed]
        · intro x
          simp [old,seed,m,takePin,run,List.getD]
      | append_singleton gs gate ih =>
        obtain ⟨P,S,M,budget,order,paid,aliases,sem⟩ := ih (fun g hg => ok g (by simp [hg]))
        obtain ⟨hop,short⟩ := ok gate (by simp)
        let source := fun i => M.getD i c0
        have sourceOK := getOK P S M aliases
        have reads (x : Fin 9 → Bool) (i : ℕ) :
            (old gs x).getD i false = takePin (run P x) (source i) := by
          rw [sem x, ← falsePin P x]
          exact List.getD_map M c0 (takePin (run P x))
        let v := fun x => gate.op.eval (gate.inputs.map fun i => (old gs x).getD i false)
        have appendOld (x : Fin 9 → Bool) : old (gs ++ [gate]) x = old gs x ++ [v x] := by
          simp only [old, List.foldl_append, List.foldl_cons, List.foldl_nil, step, v]
        have wire (p : Pin) (T : Finset ℕ) (subset : S ⊆ T) (cost : T.card ≤ S.card + 1)
            (hp : p.1 < 10 + P.length) (legal : allowed T p)
            (value : ∀ x, v x = takePin (run P x) p) :
            ∃ P S M, state (gs ++ [gate]) P S M := by
          refine ⟨P,T,M ++ [p],?_,order,?_,?_,?_⟩
          · simp only [List.length_append, List.length_singleton]
            omega
          · intro g hg
            exact ⟨keepAllowed subset (paid g hg).1, keepAllowed subset (paid g hg).2⟩
          · intro a ha
            obtain oldmem | last := List.mem_append.mp ha
            · exact ⟨(aliases a oldmem).1,keepAllowed subset (aliases a oldmem).2⟩
            · simpa only [List.mem_singleton.mp last] using And.intro hp legal
          · intro x
            rw [appendOld,sem,value]
            simp
        have binary (b : Bool) (i j : ℕ)
            (value : ∀ x, v x =
              if b then (takePin (run P x) (source i) && takePin (run P x) (source j))
              else (takePin (run P x) (source i) || takePin (run P x) (source j))) :
            ∃ P S M, state (gs ++ [gate]) P S M := by
          let g : Node := (b,source i,source j)
          let nextPin : Pin := (10 + P.length,false)
          have appendVals (x) : run (P ++ [g]) x = run P x ++ [v x] := by
            simp only [run,List.foldl_append,List.foldl_cons,List.foldl_nil,bindGate,g]
            rw [value]
          refine ⟨P ++ [g],S,M ++ [nextPin],?_,longer order g (sourceOK i).1 (sourceOK j).1,?_,?_,?_⟩
          · simp only [List.length_append,List.length_singleton]
            omega
          · intro k hk
            obtain h | h := List.mem_append.mp hk
            · exact paid k h
            · have e : k = g := List.mem_singleton.mp h
              exact e ▸ ⟨(sourceOK i).2,(sourceOK j).2⟩
          · intro a ha
            obtain h | h := List.mem_append.mp ha
            · exact ⟨by have z := (aliases a h).1; simp; omega, (aliases a h).2⟩
            · have e : a = nextPin := List.mem_singleton.mp h
              subst a
              exact ⟨by simp [nextPin],by simp [allowed,nextPin]⟩
          · intro x
            rw [appendOld,sem,List.map_append]
            have kept : M.map (takePin (run P x)) = M.map (takePin (run (P ++ [g]) x)) := by
              apply List.map_congr_left
              intro a ha
              have lt := (aliases a ha).1
              rw [appendVals]
              have bound : a.1 < (run P x).length := by rw [width]; exact lt
              exact congrArg (fun z => Bool.xor z a.2)
                (List.getD_append (run P x) [v x] false a.1 bound).symm
            rw [kept]
            have tip : takePin (run (P ++ [g]) x) nextPin = v x := by
              rw [appendVals]
              simp only [nextPin,takePin,Bool.xor_false]
              rw [List.getD_append_right _ _ _ _ (by rw [width])]
              simp [width]
            simp [tip]
        have cBound : c0.1 < 10 + P.length := by dsimp [c0]; omega
        rcases hop with ha | ho | hn
        · cases he : gate.inputs with
          | nil =>
            apply wire (neg c0) S (fun _ h => h) (by omega) cBound (by simp [allowed,neg,c0])
            intro x
            change gate.op.eval _ = _
            rw [ha,he,complemented,falsePin]
            rfl
          | cons i is =>
            cases is with
            | nil =>
              apply wire (source i) S (fun _ h => h) (by omega) (sourceOK i).1 (sourceOK i).2
              intro x
              change gate.op.eval _ = _
              rw [ha,he]
              have unary (u : Bool) : GateOp.and.eval [u] = u := by cases u <;> rfl
              simpa only [List.map_cons,List.map_nil,unary] using reads x i
            | cons j rest =>
              have none : rest = [] := by simpa [he] using short
              subst rest
              apply binary true i j
              intro x
              have pair (u w : Bool) : GateOp.and.eval [u,w] = (u && w) := by cases u <;> cases w <;> rfl
              simp only [v,ha,he,List.map_cons,List.map_nil,pair,reads,ite_true]
        · cases he : gate.inputs with
          | nil =>
            apply wire c0 S (fun _ h => h) (by omega) cBound (by simp [allowed,c0])
            intro x
            change gate.op.eval _ = _
            rw [ho,he,falsePin]
            rfl
          | cons i is =>
            cases is with
            | nil =>
              apply wire (source i) S (fun _ h => h) (by omega) (sourceOK i).1 (sourceOK i).2
              intro x
              have unary (u : Bool) : GateOp.or.eval [u] = u := by cases u <;> rfl
              simpa only [v,ho,he,List.map_cons,List.map_nil,unary] using reads x i
            | cons j rest =>
              have none : rest = [] := by simpa [he] using short
              subst rest
              apply binary false i j
              intro x
              have pair (u w : Bool) : GateOp.or.eval [u,w] = (u || w) := by cases u <;> cases w <;> rfl
              simp only [v,ho,he,List.map_cons,List.map_nil,pair,reads,Bool.false_eq_true,ite_false]
        · cases he : gate.inputs with
          | nil =>
            apply wire (neg c0) S (fun _ h => h) (by omega) cBound (by simp [allowed,neg,c0])
            intro x
            change gate.op.eval _ = _
            rw [hn,he,complemented,falsePin]
            rfl
          | cons i is =>
            let a := source i
            apply wire (neg a) (insert a.1 S) (Finset.subset_insert _ _) (Finset.card_insert_le _ _)
              (sourceOK i).1 (by intro _; exact Or.inr (Or.inr (Finset.mem_insert_self _ _)))
            intro x
            have flip (u : Bool) (xs : List Bool) : GateOp.not.eval (u::xs) = !u := rfl
            simp only [v,hn,he,List.map_cons,flip,reads,complemented,a]
    obtain ⟨gs,o⟩ := C
    cases gs with
    | nil =>
      have impossible := first (fun _ => false)
      change (List.ofFn (fun _ : Fin 9 => false)).getD 9 false = true at impossible
      rw [List.getD_eq_default _ false (by simp)] at impossible
      contradiction
    | cons g tail =>
      have firstValue (x : Fin 9 → Bool) : g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = !(x 0) := by
        let ws := List.ofFn x
        let v := g.op.eval (g.inputs.map fun i => ws.getD i false)
        obtain ⟨t,h,_⟩ := more (fun w (a : Gate) => a.op.eval (a.inputs.map fun i => w.getD i false))
          tail (ws ++ [v])
        have hx := first x
        change (tail.foldl step (ws ++ [v])).getD 9 false = _ at hx
        rw [h,List.getD_append _ _ _ _ (by simp [ws]),List.getD_append_right _ _ _ _ (by simp [ws])] at hx
        simpa [ws,v] using hx
      have final (x) : (old tail x).getD o false = target x := by
        have hx := congrFun correct x
        change (tail.foldl step (List.ofFn x ++ [g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)])).getD o false = _ at hx
        rw [firstValue] at hx
        exact hx
      have ok : ∀ a ∈ tail, (a.op = .and ∨ a.op = .or ∨ a.op = .not) ∧ a.inputs.length ≤ 2 := by
        intro a ha
        have h := fan a (by simp [ha])
        exact ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using h.1,h.2⟩
      obtain ⟨P,S,M,budget,back,pins,aliases,sem⟩ := compile tail ok
      let out := M.getD o c0
      have outOK := getOK P S M aliases o
      have agrees (x) : takePin (run P x) out = target x := by
        have hx := final x
        rw [sem,← falsePin P x] at hx
        exact (List.getD_map M c0 (takePin (run P x))).symm.trans hx
      have cap : P.length + S.card ≤ 14 := by
        change (g :: tail).length ≤ 15 at small
        simp only [List.length_cons] at small
        omega
      let left := fun j : Fin P.length => (P.get j).2.1
      let right := fun j : Fin P.length => (P.get j).2.2
      let op := fun j : Fin P.length => (P.get j).1
      let table := fun (x : Fin 9 → Bool) (i : ℕ) => (run P x).getD i false
      have inputBits (x : Fin 9 → Bool) (i : Fin 9) : table x i.val = x i := by
        obtain ⟨t,h,_⟩ := shape P x
        change (run P x).getD i.val false = _
        rw [h, List.getD_append _ _ false _ (by simp; omega),
          List.getD_append _ _ false _ (by simp),
          List.getD_eq_getElem _ _ (by simp)]
        exact List.getElem_ofFn _
      have gateTable (x : Fin 9 → Bool) (j : Fin P.length) :
          table x (10 + j.val) =
            if op j then (takePin (run P x) (left j) && takePin (run P x) (right j))
            else (takePin (run P x) (left j) || takePin (run P x) (right j)) := by
        let before := run (P.take j.val) x
        let g := P.get j
        let v := if g.1 then (takePin before g.2.1 && takePin before g.2.2)
                 else (takePin before g.2.1 || takePin before g.2.2)
        have preLength : before.length = 10 + j.val := by
          rw [show before = run (P.take j.val) x from rfl, width, List.length_take, Nat.min_eq_left j.isLt.le]
        have decomposition : P = P.take j.val ++ g :: P.drop (j.val + 1) := by
          simpa only [g, List.get_eq_getElem, List.drop_eq_getElem_cons j.isLt]
            using (List.take_append_drop j.val P).symm
        obtain ⟨extra,he,_⟩ := more (fun a (k : Node) =>
          if k.1 then (takePin a k.2.1 && takePin a k.2.2) else (takePin a k.2.1 || takePin a k.2.2))
          (P.drop (j.val + 1)) (before ++ [v])
        have full : run P x = (before ++ [v]) ++ extra := by
          calc
            run P x = run (P.take j.val ++ g :: P.drop (j.val + 1)) x := congrArg (fun t => run t x) decomposition
            _ = (before ++ [v]) ++ extra := by
              simp only [run,List.foldl_append,List.foldl_cons]
              exact he
        have early (p : Pin) (lt : p.1 < 10 + j.val) : takePin (run P x) p = takePin before p := by
          have lb : p.1 < before.length := by omega
          have lb' : p.1 < (before ++ [v]).length := by simp; omega
          rw [full]
          simp only [takePin,List.getD_append _ _ false _ lb',List.getD_append _ _ false _ lb]
        change (run P x).getD (10 + j.val) false =
          if g.1 then (takePin (run P x) g.2.1 && takePin (run P x) g.2.2)
          else (takePin (run P x) g.2.1 || takePin (run P x) g.2.2)
        rw [early _ (back j).1,early _ (back j).2,full,
          List.getD_append _ _ false _ (by simp [preLength]),
          List.getD_append_right _ _ false _ (by rw [preLength])]
        simp only [preLength,Nat.sub_self,List.getD_cons_zero,v,g]
      have sizeLB : 11 ≤ P.length := by
        by_contra! below
        obtain ⟨x,hx⟩ := unrestricted P.length op left right out table (by omega) back outOK.1
          inputBits (constZero P) gateTable
        exact hx (agrees x)
      have permissions : allowed S out ∧ ∀ j : Fin P.length, allowed S (left j) ∧ allowed S (right j) :=
        ⟨outOK.2, fun j => pins (P.get j) (List.get_mem P j)⟩
      obtain ⟨x,hx⟩ := few P.length op left right out S table (by omega) cap back outOK.1
        permissions inputBits (constZero P) gateTable
      exact hx (agrees x)
  let rowList : List ℕ := [7,13,21,37,69,133,261,325,518,524,628,644,788,804,836,1027,1041,1057,1225,
    1289,1345,1409,1560,1578,1586,1602,1640,1648,1674,1696,1736,1744,1800,1824,1856,1938]
  let truth (r : ℕ) := ([3,6,12,17,24,33,66,132,160,264,288,320] : List ℕ).any fun e => r &&& e == e
  let graph (x : Fin 9→Bool) :=
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
    (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
    (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let bits (m : Fin 512) (i : Fin 9) := m.val.testBit i.val
  let legalRow (m : Fin 512) := m.val + (if m.val.testBit 0 then 0 else 512) + (if m.val.testBit 2 then 0 else 1024)
  have legal_bits : ∀ m : Fin 512,
      List.ofFn (fun i : Fin 11 => (legalRow m).testBit i.val)=
        List.ofFn (bits m)++[!(bits m 0),!(bits m 2)] := by decide +kernel
  have legal_label : ∀ m : Fin 512, truth (legalRow m)=graph (bits m) := by decide +kernel
  have extrema : ∀ m : Fin 512,
      (truth (legalRow m)=true →
        (rowList.any fun r => truth r && (r &&& legalRow m == r))=true) ∧
      (truth (legalRow m)=false →
        (rowList.any fun r => !(truth r) && (r &&& legalRow m == legalRow m))=true) := by decide +kernel
  have spell (x : Fin 9→Bool) : ∃ m : Fin 512, bits m=x := by
    let bv : BitVec 9 := BitVec.setWidth 9 (BitVec.ofBoolListLE (List.ofFn x))
    refine ⟨bv.toFin,?_⟩
    funext i
    change bv.getLsbD i.val=x i
    unfold bv
    rw [BitVec.getLsbD_setWidth,decide_eq_true i.isLt,Bool.true_and,BitVec.getLsbD_ofBoolListLE]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some]
  have bit_subset {a b : ℕ} (eq : a &&& b=a) (i : ℕ) (on : a.testBit i=true) : b.testBit i=true := by
    have h := congrArg (fun x : ℕ => x.testBit i) eq
    change (a &&& b).testBit i=a.testBit i at h
    simpa only [Nat.testBit_and,on,Bool.true_and] using h
  have noSuffix (C : Circuit) (legal : FanInTwo C) (size : C.size ≤ 13) :
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x++[!x 0,!x 2]) ≠ graph x := by
    by_contra! fits
    let g : Gate := ⟨.not,[0]⟩
    let h : Gate := ⟨.not,[2]⟩
    let D : Circuit := ⟨g :: h :: C.gates,C.output⟩
    let advance := fun (w : List Bool) (k : Gate) => w ++ [k.op.eval (k.inputs.map (fun i => w.getD i false))]
    let inputs := fun (x : Fin 9 → Bool) => List.ofFn x ++ [!x 0] ++ [!x 2]
    have well : FanInTwo D := by
      intro k mem
      change k ∈ g :: h :: C.gates at mem
      rcases List.mem_cons.mp mem with rfl|mem
      · exact ⟨Or.inr (Or.inr rfl),by decide⟩
      rcases List.mem_cons.mp mem with rfl|mem
      · exact ⟨Or.inr (Or.inr rfl),show (1 : ℕ) ≤ 2 from (by decide)⟩
      · exact legal _ mem
    have raw (x : Fin 9 → Bool) (i : Fin 9) : (List.ofFn x).getD i.val false=x i := by
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt),List.getElem_ofFn]
    have first (x : Fin 9 → Bool) : advance (List.ofFn x) g=List.ofFn x ++ [!x 0] := by
      change List.ofFn x ++ [!((List.ofFn x).getD 0 false)] = _
      have atZero : (List.ofFn x).getD 0 false=x 0 := raw x 0
      rw [atZero]
    have initial (x : Fin 9 → Bool) : advance (advance (List.ofFn x) g) h=inputs x := by
      rw [first]
      let z := List.ofFn x ++ [!x 0]
      have same (i : Fin 9) : z.getD i.val false=x i := by
        rw [show z.getD i.val false=(List.ofFn x).getD i.val false from List.getD_append _ _ _ _ (by simp),raw]
      change z ++ [!(z.getD 2 false)] = z ++ [!x 2]
      have atTwo : z.getD 2 false=x 2 := same 2
      rw [atTwo]
    have preserve (gs : List Gate) (w : List Bool) (i : ℕ) (early : i<w.length) :
        (gs.foldl advance w).getD i false=w.getD i false := by
      induction gs generalizing w with
      | nil => rfl
      | cons k gs ih =>
        rw [List.foldl_cons,ih (advance w k) (by simp only [advance,List.length_append,List.length_cons,List.length_nil];omega)]
        exact List.getD_append _ _ _ _ early
    have stored (x : Fin 9 → Bool) : (D.wires (List.ofFn x)).getD 9 false = !x 0 := by
      change ((h::C.gates).foldl advance (advance (List.ofFn x) g)).getD 9 false = _
      rw [first,preserve _ _ _ (by simp),List.getD_append_right _ _ _ _ (by simp),List.length_ofFn,Nat.sub_self]
      rfl
    have correct : circuitFun 9 D = (fun x : Fin 9 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
        (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
        (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
      funext x
      change (C.gates.foldl advance (advance (advance (List.ofFn x) g) h)).getD C.output false=_
      rw [initial]
      exact fits x
    have bound := firstNot D well stored correct
    change 16 ≤ (g :: h :: C.gates).length at bound
    change C.gates.length ≤ 13 at size
    simp only [List.length_cons] at bound
    omega
  intro sat
  obtain ⟨C,fan,size,monotone,fit⟩ := decodeCNF 11 13 truth rowList sat
  obtain ⟨x,bad⟩ := noSuffix C fan size.le
  apply bad
  obtain ⟨m,hm⟩ := spell x
  have src : List.ofFn (fun i : Fin 11 => (legalRow m).testBit i.val)=List.ofFn x++[!x 0,!x 2] := by
    simpa only [hm] using legal_bits m
  have lab := (legal_label m).trans (congrArg graph hm)
  rw [←src,←lab]
  let z := fun i : Fin 11 => (legalRow m).testBit i.val
  cases h : truth (legalRow m) with
  | true =>
    obtain ⟨r,mem,ok⟩ := List.any_eq_true.mp ((extrema m).1 h)
    obtain ⟨yes,contained⟩ := Bool.and_eq_true_iff.mp ok
    have sub : r &&& legalRow m=r := by simpa using contained
    have small := (fit r mem).trans yes
    exact monotone (fun i : Fin 11 => r.testBit i.val) z
      (fun i hi => bit_subset sub i.val hi) small
  | false =>
    obtain ⟨r,mem,ok⟩ := List.any_eq_true.mp ((extrema m).2 h)
    obtain ⟨no,contained⟩ := Bool.and_eq_true_iff.mp ok
    have off : truth r=false := by simpa using no
    have sub : r &&& legalRow m=legalRow m := by simpa using contained
    have order : legalRow m &&& r=legalRow m := (Nat.and_comm ..).trans sub
    have negative := (fit r mem).trans off
    apply Bool.eq_false_iff.mpr
    intro on
    have bad := monotone z (fun i : Fin 11 => r.testBit i.val)
      (fun i hi => bit_subset order i.val hi) on
    exact Bool.noConfusion (negative.symm.trans bad)
