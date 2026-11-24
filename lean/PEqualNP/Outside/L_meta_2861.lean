import PEqualNP.Defs

-- The wire evaluation identities follow L_meta_2319 and L_meta_616.
-- The exchange argument works for every binary gate operation with the stated law.
namespace PEqualNP.Outside.L_meta_2861
open PEqualNP.CircuitLowerBounds
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    exact getD_append_left_lt w _ i hi

lemma foldl_step_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  apply getD_ge_len
  rw [foldl_step_len]
  exact hi

lemma foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i => if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : w.length < (step w g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [foldl_step_getD_lt gs (step w g0) w.length hlt]
      have hself : (step w g0).getD w.length false = g0.op.eval (g0.inputs.map fun i => w.getD i false) :=
        getD_append_self w _
      rw [hself]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
        exact (getD_append_left_lt w _ i hi).symm
      · simp only [hi, ↓reduceIte]
        exact getD_ge_len w i (Nat.le_of_not_lt hi)
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ← hlen]
      exact ih (step w g0) j' hj

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

lemma wires_gate_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun i => if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
  have h := foldl_step_gate C.gates (List.ofFn x) j g hj
  simpa only [List.length_ofFn, ← wires_eq_foldl] using h

lemma ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

lemma wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
  rw [wires_eq_foldl, foldl_step_getD_lt C.gates (List.ofFn x) w (by simp [hw]), ofFn_getD_lt]

lemma wires_oob {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    (C.wires (List.ofFn x)).getD w false = false := by
  rw [wires_eq_foldl]
  exact foldl_step_getD_ge C.gates (List.ofFn x) w (by simp [hw])


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (wire : ℕ) :=
  (C.wires (List.ofFn x)).getD wire false

lemma readValue {n : ℕ} (C : Circuit) (back : ReadsBack n C) (x : Fin n → Bool)
    (k : ℕ) (valid : k<C.gates.length) : value C x (n+k) =
    (gateAt C k).op.eval ((gateAt C k).inputs.map (value C x)) := by
  have present : C.gates[k]? = some (gateAt C k) := by
    rw [List.getElem?_eq_getElem valid]
    unfold gateAt
    rw [List.getD_eq_getElem _ _ valid]
  rw [value,wires_gate_ofFn C x k _ present]
  apply congrArg (gateAt C k).op.eval
  apply List.map_congr_left
  intro w hw
  simp only [if_pos (back k valid w hw),value]

def rotate (C : Circuit) (n i j a b c : ℕ) (op : GateOp) : Circuit :=
  ⟨(C.gates.set i ⟨op,[a,c]⟩).set j ⟨op,[n+i,b]⟩,C.output⟩

theorem exchange (n : ℕ) (C : Circuit) (i j a b c : ℕ) (op : GateOp)
    (law : ∀ x y z : Bool, op.eval [op.eval [x,z],y] = op.eval [op.eval [x,y],z])
    (back : ReadsBack n C) (jok : j<C.gates.length) (ij : i<j)
    (iop : (gateAt C i).op=op) (ii : (gateAt C i).inputs=[a,b])
    (jop : (gateAt C j).op=op) (ji : (gateAt C j).inputs=[n+i,c]) (early : c<n+i)
    (alone : ∀ k<C.gates.length, k≠j → n+i ∉ (gateAt C k).inputs) :
    let D := rotate C n i j a b c op
    ReadsBack n D ∧ D.size=C.size ∧ ∀ (x : Fin n → Bool) (w : ℕ), w≠n+i →
       value D x w = value C x w := by
  let D := rotate C n i j a b c op
  have iok : i<C.gates.length := lt_trans ij jok
  have ai := back i iok a (by simp [ii])
  have bi := back i iok b (by simp [ii])
  have len : D.gates.length = C.gates.length := by simp [D,rotate]
  have first : gateAt D i = ⟨op,[a,c]⟩ := by
    simp only [D,rotate,gateAt,List.getD_eq_getElem?_getD,
      List.getElem?_set_ne (Ne.symm (Nat.ne_of_lt ij)),List.getElem?_set_self iok,Option.getD_some]
  have last : gateAt D j = ⟨op,[n+i,b]⟩ := by
    simp [D,rotate,gateAt,List.getD_eq_getElem?_getD,jok]
  have rest (k : ℕ) (ki : k≠i) (kj : k≠j) : gateAt D k = gateAt C k := by
    simp [D,rotate,gateAt,List.getD_eq_getElem?_getD,List.getElem?_set_ne (Ne.symm ki),
      List.getElem?_set_ne (Ne.symm kj)]
  have newBack : ReadsBack n D := by
    intro k hk w hw
    by_cases eqi : k=i
    · subst k
      rw [first] at hw
      rcases List.mem_cons.mp hw with rfl | h
      · exact ai
      · have eq := List.mem_singleton.mp h
        exact eq ▸ early
    by_cases eqj : k=j
    · subst k
      rw [last] at hw
      rcases List.mem_cons.mp hw with rfl | h
      · omega
      · have eq := List.mem_singleton.mp h
        omega
    rw [rest k eqi eqj] at hw
    exact back k (len ▸ hk) w hw
  refine ⟨newBack,len,?_⟩
  intro x w
  have iBefore : value C x (n+i) = op.eval [value C x a,value C x b] := by
    simp only [readValue C back x i iok,iop,ii,List.map_cons,List.map_nil]
  have jBefore : value C x (n+j) = op.eval [value C x (n+i),value C x c] := by
    simp only [readValue C back x j jok,jop,ji,List.map_cons,List.map_nil]
  have iAfter : value D x (n+i) = op.eval [value D x a,value D x c] := by
    simp only [readValue D newBack x i (by omega),first,List.map_cons,List.map_nil]
  have jAfter : value D x (n+j) = op.eval [value D x (n+i),value D x b] := by
    simp only [readValue D newBack x j (by omega),last,List.map_cons,List.map_nil]
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro distinct
    by_cases raw : w<n
    · exact (wires_input D x w raw).trans (wires_input C x w raw).symm
    by_cases beyond : n+C.gates.length≤w
    · exact (wires_oob D x w (by omega)).trans (wires_oob C x w beyond).symm
    obtain ⟨k,rfl⟩ : ∃ k, w=n+k := ⟨w-n,by omega⟩
    have inRange : k<C.gates.length := by omega
    by_cases atLast : k=j
    · subst k
      rw [jAfter,jBefore,iAfter,iBefore,ih a (by omega) (by omega),ih b (by omega) (by omega),
        ih c (by omega) (by omega)]
      exact law _ _ _
    have atOther : k≠i := by omega
    rw [readValue D newBack x k (by omega),rest k atOther atLast,readValue C back x k inRange]
    apply congrArg (gateAt C k).op.eval
    apply List.map_congr_left
    intro u hu
    apply ih u (back k inRange u hu)
    rintro rfl
    exact alone k inRange atLast hu

end PEqualNP.Outside.L_meta_2861

theorem PEqualNP.Outside.L_meta_2861 :
  ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (i j a b c : ℕ), PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → j < C.gates.length → i < j → (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs = [a, b] → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [n + i, c] → c < n + i → (∀ k < C.gates.length, k ≠ j → n + i ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) → C.output ≠ n + i → PEqualNP.MetaComplexity.NestedCover.ReadsBack n (⟨(C.gates.set i ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, c]⟩).set j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [n + i, b]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧ (⟨(C.gates.set i ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, c]⟩).set j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [n + i, b]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size ∧ ∀ x : Fin n → Bool, (⟨(C.gates.set i ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, c]⟩).set j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [n + i, b]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x) = C.eval (List.ofFn x) := by

  intro n C i j a b c back hj ij iop ii jop ji early alone out
  have law : ∀ x y z : Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval [PEqualNP.CircuitLowerBounds.GateOp.and.eval [x,z],y] =
      PEqualNP.CircuitLowerBounds.GateOp.and.eval [PEqualNP.CircuitLowerBounds.GateOp.and.eval [x,y],z] := by decide +kernel
  obtain ⟨legal,cost,same⟩ := PEqualNP.Outside.L_meta_2861.exchange n C i j a b c .and law back hj ij iop ii jop ji early alone
  exact ⟨legal,cost,fun x => same x C.output out⟩
