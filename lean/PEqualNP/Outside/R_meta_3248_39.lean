import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- An edge and one of its endpoints force a negation. Absorb signs into the binary
-- gates, then restrict vertex six to false. Its raw bit is essential even while
-- the extra disjunction is fixed, so the restriction saves another gate.
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_3248_39
    (specialize : ∀ (n m : ℕ) (r : Fin n → Option (Fin m)) (D : BinaryCircuit),
      (∀ g ∈ D.gates, ∃ a b : Bool, ∀ u v, g.op u v = ((u != a) && (v != b))) →
      n ≤ D.output →
      (∃ a b : Fin n → Bool, (∀ i, r i ≠ none → a i = b i) ∧
        D.eval (List.ofFn a) ≠ D.eval (List.ofFn b)) →
      ∃ (E : BinaryCircuit) (p : Bool), E.size < D.size ∧
        (∀ g ∈ E.gates, ∃ a b : Bool, ∀ u v, g.op u v = ((u != a) && (v != b))) ∧
        ∀ y : Fin m → Bool, D.eval (List.ofFn fun i => ((r i).map y).getD false) =
          (E.eval (List.ofFn y ++ [false]) != p))
    (firstGate : let edges : List (Fin 8 × Fin 8) :=
        [(0,1),(1,2),(2,3),(0,4),(1,5),(2,6),(3,7),(4,6),(5,7),(7,4)]
      let f (x : Fin 8 → Bool) := edges.any fun e => x e.1 && x e.2
      ∀ (D : BinaryCircuit) (p : Bool), D.size ≤ 11 →
        (∀ g ∈ D.gates, ∃ a b : Bool, ∀ u v, g.op u v = ((u != a) && (v != b))) →
        (∀ x, (D.eval (List.ofFn x ++ [false]) != p) = f x) →
        ∃ (j : Fin 8) (A : BinaryCircuit) (s : Bool), (j = 2 ∨ j = 4) ∧ A.size ≤ 10 ∧
          (∀ g ∈ A.gates, ∃ a b : Bool, ∀ u v, g.op u v = ((u != a) && (v != b))) ∧
          ∀ x, (A.eval (List.ofFn x ++ [false, (!x 1) && (!x j)]) != s) = f x)
    (finiteCheck : let edges : List (Fin 8 × Fin 8) :=
        [(0,1),(1,2),(2,3),(0,4),(1,5),(2,6),(3,7),(4,6),(5,7),(7,4)]
      ∀ (j : Fin 8), j = 2 ∨ j = 4 →
      ∀ (P : List.Vector ((Fin 21 × Bool) × (Fin 21 × Bool)) 10) (o : Fin 21) (s : Bool),
        ∃ x : Fin 8 → Bool, ((P.toList.foldl (fun (w : List Bool) op =>
          w ++ [((w.getD op.1.1.val false != op.1.2) && (w.getD op.2.1.val false != op.2.2))])
          (List.ofFn x ++ [false, (!x 1) && (!x j)])).getD o.val false != s) ≠
          (edges.any fun e => x e.1 && x e.2)) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 ≠ (0 : Fin (9 : ℕ)) → x2 ≠ (6 : Fin (9 : ℕ)) → PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → ∃ (x8 : Fin (9 : ℕ) → Bool), x3.eval ((List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ))]).set ↑x2 !x8 x2) ≠ x1 x8 := by
  have normalize
      (n : ℕ) (C : Circuit) (flip : Fin n → Bool) (fan : FanInTwo C)
      (hasNot : ∃ g ∈ C.gates, g.op = GateOp.not) :
      ∃ (D : BinaryCircuit) (p : Bool), D.size < C.size ∧
        (∀ g ∈ D.gates, ∃ a b : Bool, ∀ u v, g.op u v = ((u != a) && (v != b))) ∧
        ∀ x : Fin n → Bool,
          C.eval (List.ofFn fun i => x i != flip i) = (D.eval (List.ofFn x ++ [false]) != p) := by
    let oldStep (w : List Bool) (g : Gate) :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    let newStep (w : List Bool) (g : BinaryGate) :=
      w ++ [g.op (w.getD g.left false) (w.getD g.right false)]
    let ok (g : BinaryGate) := ∃ a b : Bool, ∀ u v, g.op u v = ((u != a) && (v != b))
    let read (w : List Bool) (p : ℕ × Bool) := w.getD p.1 false != p.2
    let source (m : ℕ → ℕ × Bool) (is : List ℕ) (j : ℕ) (b : Bool) : ℕ × Bool :=
      is[j]?.elim (n,b) m
    have packedLen (gs : List BinaryGate) (w : List Bool) :
        (gs.foldl newStep w).length = w.length + gs.length := by
      induction gs generalizing w with
      | nil => simp
      | cons g gs ih => simp only [List.foldl_cons, ih, newStep, List.length_append,
          List.length_cons, List.length_nil]; omega
    have keep (gs : List BinaryGate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
        (gs.foldl newStep w).getD i false = w.getD i false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons, ih _ (by simp [newStep]; omega)]
        exact List.getD_append _ _ _ _ hi
    have added (w : List Bool) (b : Bool) (i : ℕ) :
        (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
      by_cases before : i < w.length
      · rw [List.getD_append _ _ _ _ before, ite_eq_right (by omega)]
      · by_cases eq : i = w.length
        · subst i
          simp [List.getD]
        · rw [ite_eq_right eq, List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by omega)]
    have binaryValue (mode : Bool) (xs : List Bool) (len : xs.length ≤ 2) :
        (if mode then xs.any id else xs.all id) =
        ((((xs.getD 0 (!mode)) != mode) && ((xs.getD 1 (!mode)) != mode)) != mode) := by
      rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c,cs⟩⟩⟩
      · cases mode <;> rfl
      · cases mode <;> cases a <;> rfl
      · cases mode <;> cases a <;> cases b <;> rfl
      · simp at len
    have xorNest (a b c : Bool) : (a != (b != c)) = ((a != b) != c) := by
      cases a <;> cases b <;> cases c <;> rfl
    have xorFlip (a b : Bool) : (a != !b) = !(a != b) := by
      cases a <;> cases b <;> rfl
    let rows := Fin n → Bool
    let admissible (g : Gate) := (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2
    have translate (gs : List Gate) (allowed : ∀ g ∈ gs, admissible g)
        (k t : ℕ) (hn : n < t) (w z : rows → List Bool)
        (wk : ∀ x, (w x).length = k) (zt : ∀ x, (z x).length = t)
        (fixed : ∀ x, (z x).getD n false = false)
        (m : ℕ → ℕ × Bool) (valid : ∀ i, (m i).1 < t)
        (equiv : ∀ x i, (w x).getD i false = read (z x) (m i)) :
        ∃ (ss : List BinaryGate) (remap : ℕ → ℕ × Bool),
          ss.length ≤ gs.length ∧ ((∃ g ∈ gs, g.op = GateOp.not) → ss.length < gs.length) ∧
          (∀ g ∈ ss, ok g) ∧ ∀ x i, (gs.foldl oldStep (w x)).getD i false =
            read (ss.foldl newStep (z x)) (remap i) := by
      induction gs generalizing k t w z m with
      | nil =>
        exact ⟨[],m,by simp,by simp,by simp,equiv⟩
      | cons g gs ih =>
        obtain ⟨ops,small⟩ := allowed g (by simp)
        have sourceValid (j b) : (source m g.inputs j b).1 < t := by
          unfold source
          cases h : g.inputs[j]? with
          | none => exact hn
          | some i => exact valid i
        have sourceEq (x : rows) (j : ℕ) (b : Bool) :
            (g.inputs.map fun i => (w x).getD i false).getD j b =
              read (z x) (source m g.inputs j b) := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_map, source]
          cases h : g.inputs[j]? with
          | none =>
            change b = ((z x).getD n false != b)
            rw [fixed]; exact (Bool.false_bne b).symm
          | some i =>
            simpa only [List.getD_eq_getElem?_getD, Option.map_some, Option.getD_some, Option.elim_some] using equiv x i
        have one : ∃ (bs : List BinaryGate) (q : ℕ × Bool), bs.length ≤ 1 ∧
            (g.op = GateOp.not → bs = []) ∧ (∀ h ∈ bs, ok h) ∧ q.1 < t + bs.length ∧
            ∀ x : rows, g.op.eval (g.inputs.map fun i => (w x).getD i false) =
              read (bs.foldl newStep (z x)) q := by
          by_cases neg : g.op = GateOp.not
          · let a := source m g.inputs 0 false
            refine ⟨[],(a.1,!a.2),by simp,fun _ => rfl,by simp,by simpa [a] using sourceValid 0 false,?_⟩
            intro x
            rw [neg]
            change (!((g.inputs.map fun i => (w x).getD i false).headD false)) = _
            simp only [List.headD_eq_getD, sourceEq, List.foldl_nil, read, a, xorFlip]
          · have modeExists : ∃ mode : Bool, g.op = if mode then GateOp.or else GateOp.and := by
              rcases ops with a | o | z
              · exact ⟨false,a⟩
              · exact ⟨true,o⟩
              · exact (neg z).elim
            obtain ⟨mode,tag⟩ := modeExists
            let a := source m g.inputs 0 (!mode)
            let b := source m g.inputs 1 (!mode)
            let h : BinaryGate := ⟨fun u v => (u != (a.2 != mode)) && (v != (b.2 != mode)), a.1, b.1⟩
            refine ⟨[h],(t,mode),by simp,fun h => (neg h).elim,?_,by simp,?_⟩
            · intro q hq
              obtain rfl : q = h := by simpa using hq
              exact ⟨_,_,fun _ _ => rfl⟩
            · intro x
              let inputs := g.inputs.map fun i => (w x).getD i false
              have val : g.op.eval inputs = if mode then inputs.any id else inputs.all id := by
                cases mode <;> rw [tag] <;> rfl
              rw [val, binaryValue _ _ (by simpa [inputs] using small)]
              change _ = ((newStep (z x) h).getD t false != mode)
              simp only [newStep, added, zt, ite_true, h, xorNest, inputs, sourceEq, read, a, b]
        obtain ⟨bs,q,oneBound,noneNeg,basis,validQ,evalQ⟩ := one
        let next (i : ℕ) := if i = k then q else m i
        let z' (x : rows) := bs.foldl newStep (z x)
        have agrees (x : rows) (i : ℕ) :
            (oldStep (w x) g).getD i false = read (z' x) (next i) := by
          rw [show oldStep (w x) g = _ from rfl, added, wk]
          by_cases hi : i = k
          · simpa only [ite_eq_left hi, next, z'] using evalQ x
          · simp only [ite_eq_right hi, next, z', read,
              keep bs (z x) (m i).1 (by rw [zt]; exact valid i)]
            exact equiv x i
        obtain ⟨tailGates,remap,bound,strict,basis',rest⟩ :=
          ih (fun h hh => allowed h (List.mem_cons_of_mem _ hh))
            (k+1) (t+bs.length) (by omega) (fun x => oldStep (w x) g) z'
            (by intro x; simp [oldStep,wk])
            (by intro x; simp [z',packedLen,zt])
            (fun x => (keep bs (z x) n (by rw [zt]; exact hn)).trans (fixed x))
            next (by intro i; by_cases hi : i = k
                     · simpa only [next, ite_eq_left hi] using validQ
                     · simp only [next, ite_eq_right hi]; have := valid i; omega) agrees
        refine ⟨bs ++ tailGates,remap,?_,?_,?_,?_⟩
        · simp only [List.length_append,List.length_cons]; omega
        · rintro ⟨h,mem,op⟩
          rcases List.mem_cons.mp mem with first | later
          · subst h
            simp [noneNeg op]; omega
          · have := strict ⟨h,later,op⟩
            simp only [List.length_append,List.length_cons]; omega
        · intro h mem
          exact (List.mem_append.mp mem).elim (basis h) (basis' h)
        · simpa only [List.foldl_append, List.foldl_cons, z'] using rest
    let raw (x : rows) := List.ofFn fun i => x i != flip i
    let stored (x : rows) := List.ofFn x ++ [false]
    let initial (i : ℕ) : ℕ × Bool := if h : i < n then (i,flip ⟨i,h⟩) else (n,false)
    have fixedInput (x : rows) : (stored x).getD n false = false := by
      rw [show stored x = List.ofFn x ++ [false] from rfl, added, List.length_ofFn]
      simp
    have initEq (x : rows) (i : ℕ) : (raw x).getD i false = read (stored x) (initial i) := by
      by_cases h : i < n
      · simp only [raw, stored, read, initial, dite_eq_left h]
        rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using h),
          List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using h),
          List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using h)]
        simp only [List.getElem_ofFn]
      · rw [List.getD_eq_default _ _ (by simpa [raw] using Nat.le_of_not_gt h)]
        simp only [read, initial, dite_eq_right h, fixedInput, Bool.bne_false]
    have admiss (g) (mem : g ∈ C.gates) : admissible g := by
      simpa only [admissible, Set.mem_insert_iff, Set.mem_singleton_iff] using fan g mem
    obtain ⟨ss,m,_,strict,basis,sim⟩ := translate C.gates admiss n (n+1) (by omega)
      raw stored (by simp [raw]) (by simp [stored])
      fixedInput initial (by intro i; unfold initial; split <;> dsimp <;> omega) initEq
    exact ⟨⟨ss,(m C.output).1⟩,(m C.output).2,strict hasNot,basis,fun x => sim x C.output⟩
  let edges : List (Fin 9 × Fin 9) :=
    [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
  let target (x : Fin 9 → Bool) := edges.any fun e => x e.1 && x e.2
  let base (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 6]
  let row (v : Fin 9) (x : Fin 9 → Bool) := (base x).set v.val (!(x v))
  let point (x : Fin 9 → Bool) (i : Fin 10) := (base x).getD i.val false
  let flip (v : Fin 9) (i : Fin 10) := i.val == v.val
  have baseTab (x : Fin 9 → Bool) : List.ofFn (point x) = base x := by
    apply List.ext_getElem
    · simp [base]
    · intro i hi hj
      simp only [List.getElem_ofFn, point]
      exact List.getD_eq_getElem _ _ hj
  have flipTab (v : Fin 9) (x : Fin 9 → Bool) :
      List.ofFn (fun i => point x i != flip v i) = row v x := by
    apply List.ext_getElem
    · simp [row, base]
    · intro i hi hj
      by_cases eq : i = v.val
      · subst i
        simp only [List.getElem_ofFn, flip, beq_self_eq_true, Bool.bne_true, row,
          List.getElem_set_self, point, base]
        rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using v.isLt),
          List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using v.isLt),
          List.getElem_ofFn]
      · simp only [List.getElem_ofFn, point, flip, beq_false_of_ne eq,
          Bool.bne_false, row, List.getElem_set_ne (Ne.symm eq)]
        exact List.getD_eq_getElem _ _ (by simpa [row] using hj)
  let neighbor (v : Fin 9) : Fin 9 := ![1,0,1,2,0,0,1,2,3] v
  let single (v : Fin 9) (i : Fin 9) := i == neighbor v
  let pair (v : Fin 9) (i : Fin 9) := (i == neighbor v) || (i == v)
  have witness : ∀ v : Fin 9, v ≠ 0 → v ≠ 6 →
      target (pair v) = true ∧ target (single v) = false ∧
      ∀ i : Fin 10, (row v (pair v)).getD i false = true →
        (row v (single v)).getD i false = true := by decide +kernel
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let le (u v : List Bool) := u.length = v.length ∧
    ∀ i : ℕ, u.getD i false = true → v.getD i false = true
  have stepMono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
      (u v : List Bool) (h : le u v) : le (step u g) (step v g) := by
    have last : g.op.eval (g.inputs.map fun i => u.getD i false) = true →
        g.op.eval (g.inputs.map fun i => v.getD i false) = true := by
      rcases hop with ha | ho
      · rw [ha]
        change (g.inputs.map fun i => u.getD i false).all id = true →
          (g.inputs.map fun i => v.getD i false).all id = true
        simpa [List.all_map] using
          (fun (all : ∀ i ∈ g.inputs, u.getD i false = true) i hi => h.2 i (all i hi))
      · rw [ho]
        change (g.inputs.map fun i => u.getD i false).any id = true →
          (g.inputs.map fun i => v.getD i false).any id = true
        simpa [List.any_map] using
          (fun (some : ∃ i ∈ g.inputs, u.getD i false = true) =>
            some.elim fun i hi => ⟨i, hi.1, h.2 i hi.2⟩ :
              (∃ i ∈ g.inputs, u.getD i false = true) → ∃ i ∈ g.inputs, v.getD i false = true)
    refine ⟨by simp [step, h.1], ?_⟩
    intro i
    by_cases inside : i < u.length
    · simpa only [step, List.getD_append _ _ _ _ inside,
        List.getD_append _ _ _ _ (inside.trans_eq h.1)] using h.2 i
    · simp only [step, List.getD_append_right _ _ _ _ (by omega : u.length ≤ i),
        List.getD_append_right _ _ _ _ (by have := h.1; omega : v.length ≤ i), ← h.1]
      cases i - u.length with
      | zero => exact last
      | succ k => simp [List.getD]
  have foldMono (gs : List Gate) (ops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
      ∀ (u v : List Bool), le u v → le (gs.foldl step u) (gs.foldl step v) := by
    induction gs with
    | nil => exact fun _ _ h => h
    | cons g rest ih =>
      intro u v h
      exact ih (fun t ht => ops t (List.mem_cons_of_mem _ ht)) _ _
        (stepMono g (ops g (by simp)) u v h)
  change ∀ (v : Fin 9) (C : Circuit), v ≠ 0 → v ≠ 6 → FanInTwo C → C.size ≤ 13 →
    ∃ x, C.eval (row v x) ≠ target x
  intro v C v0 v6 fan small
  by_contra! correct
  have needsNot : ∃ g ∈ C.gates, g.op = GateOp.not := by
    by_contra! none
    have ops (g) (hg : g ∈ C.gates) : g.op = GateOp.and ∨ g.op = GateOp.or := by
      have allowed := (fan g hg).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at allowed
      rcases allowed with a | b | n
      · exact Or.inl a
      · exact Or.inr b
      · exact False.elim (none g hg n)
    obtain ⟨edge, singleton, ordered⟩ := witness v v0 v6
    have start : le (row v (pair v)) (row v (single v)) := by
      refine ⟨by simp [row, base], ?_⟩
      intro i
      by_cases hi : i < 10
      · exact ordered ⟨i,hi⟩
      · rw [List.getD_eq_default _ _ (by simp [row, base]; omega)]
        simp
    have rise := (foldMono C.gates ops _ _ start).2 C.output
    change C.eval (row v (pair v)) = true → C.eval (row v (single v)) = true at rise
    rw [correct, correct, edge, singleton] at rise
    exact Bool.noConfusion (rise rfl)
  obtain ⟨D,p,short,basis,eq⟩ := normalize 10 C (flip v) fan needsNot
  let full (x : Fin 9 → Bool) := base x ++ [false]
  have computesTarget (x : Fin 9 → Bool) : (D.eval (full x) != p) = target x := by
    have sim := eq (point x)
    rw [flipTab, baseTab] at sim
    exact sim.symm.trans (correct x)
  let readFull (x : Fin 9 → Bool) (i : Fin 11) := (full x).getD i.val false
  have fullTab (x : Fin 9 → Bool) : List.ofFn (readFull x) = full x := by
    apply List.ext_getElem
    · simp [full,base]
    · intro i hi hj
      simp only [List.getElem_ofFn,readFull]
      exact List.getD_eq_getElem _ _ hj
  let bstep (w : List Bool) (g : BinaryGate) :=
    w ++ [g.op (w.getD g.left false) (w.getD g.right false)]
  have keepRaw (gs : List BinaryGate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl bstep w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [bstep]; omega)]
      exact List.getD_append _ _ _ _ hi
  have noLiteral : ∀ (i : Fin 11) (phase : Bool), ∃ x : Fin 9 → Bool,
      (readFull x i != phase) ≠ target x := by decide +kernel
  have outputGate : 11 ≤ D.output := by
    by_contra! inside
    obtain ⟨x,miss⟩ := noLiteral ⟨D.output,inside⟩ p
    apply miss
    have same := computesTarget x
    change ((D.gates.foldl bstep (full x)).getD D.output false != p) = _ at same
    rwa [keepRaw _ _ _ (by simpa [full,base] using inside)] at same
  let r : Fin 11 → Option (Fin 8) :=
    ![some 1,some 0,some 4,some 7,some 5,some 2,none,some 6,some 3,some 1,none]
  let before (i : Fin 9) := (i == 0) || (i == 8)
  let after (i : Fin 9) := (i == 0) || (i == 8) || (i == 6)
  have test : (∀ i, r i ≠ none → readFull before i = readFull after i) ∧
      target before = false ∧ target after = true := by decide +kernel
  have different : D.eval (List.ofFn (readFull before)) ≠ D.eval (List.ofFn (readFull after)) := by
    rw [fullTab,fullTab]
    intro equal
    have a := computesTarget before
    have b := computesTarget after
    rw [equal,b,test.2.1,test.2.2] at a
    exact Bool.noConfusion a
  obtain ⟨E,q,smaller,basisE,restricted⟩ :=
    specialize 11 8 r D basis outputGate ⟨_,_,test.1,different⟩
  let lift (y : Fin 8 → Bool) : Fin 9 → Bool :=
    ![y 1,y 0,y 4,y 7,y 5,y 2,false,y 6,y 3]
  let subedges : List (Fin 8 × Fin 8) :=
    [(0,1),(1,2),(2,3),(0,4),(1,5),(2,6),(3,7),(4,6),(5,7),(7,4)]
  have rowsAgree : ∀ y : Fin 8 → Bool,
      List.ofFn (fun i => ((r i).map y).getD false) = full (lift y) := by decide +kernel
  have graphAgree : ∀ y : Fin 8 → Bool, target (lift y) =
      (subedges.any fun e => y e.1 && y e.2) := by decide +kernel
  have assoc (a b c : Bool) : (a != (b != c)) = ((a != b) != c) := by
    cases a <;> cases b <;> cases c <;> rfl
  have sliceCorrect (y : Fin 8 → Bool) : (E.eval (List.ofFn y ++ [false]) != (q != p)) =
      (subedges.any fun e => y e.1 && y e.2) := by
    have cut := restricted y
    rw [rowsAgree] at cut
    have ans := computesTarget (lift y)
    rw [cut,graphAgree] at ans
    exact (assoc _ _ _).trans ans
  obtain ⟨j,A,s,jchoice,budget,basisA,computesSlice⟩ :=
    firstGate E (q != p) (by omega) basisE sliceCorrect
  let inputs (x : Fin 8 → Bool) := List.ofFn x ++ [false, (!x 1) && (!x j)]
  let Code := (Fin 21 × Bool) × (Fin 21 × Bool)
  let run (w : List Bool) (op : Code) :=
    w ++ [((w.getD op.1.1.val false != op.1.2) && (w.getD op.2.1.val false != op.2.2))]
  let cap (i : ℕ) : Fin 21 := ⟨min i 20,by omega⟩
  let encode (g : BinaryGate) : Code :=
    ((cap g.left,g.op false false || g.op false true),
     (cap g.right,g.op false false || g.op true false))
  have capRead (w : List Bool) (hw : w.length ≤ 20) (i : ℕ) :
      w.getD (cap i).val false = w.getD i false := by
    change w.getD (min i 20) false = w.getD i false
    by_cases hi : i ≤ 20
    · rw [Nat.min_eq_left hi]
    · rw [Nat.min_eq_right (by omega), List.getD_eq_default _ _ hw,
        List.getD_eq_default _ _ (by omega)]
  have encOne (w : List Bool) (hw : w.length ≤ 20) (g : BinaryGate) (hg : g ∈ A.gates) :
      run w (encode g) = bstep w g := by
    obtain ⟨a,b,h⟩ := basisA g hg
    simp only [run,encode,bstep,capRead _ hw,h]
    cases a <;> cases b <;> cases w.getD g.left false <;> cases w.getD g.right false <;> rfl
  have encList (gs : List BinaryGate) (hg : ∀ g ∈ gs, g ∈ A.gates)
      (w : List Bool) (hw : w.length + gs.length ≤ 20) :
      (gs.map encode).foldl run w = gs.foldl bstep w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.map_cons,List.foldl_cons]
      rw [encOne _ (by omega) _ (hg g (by simp))]
      apply ih (fun h hh => hg h (List.mem_cons_of_mem _ hh))
      simp only [bstep,List.length_append,List.length_cons,List.length_nil] at *
      omega
  have wireLen (gs : List BinaryGate) (w : List Bool) :
      (gs.foldl bstep w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      simp only [List.foldl_cons,ih,bstep,List.length_append,List.length_cons,List.length_nil]; omega
  have padLen (ps : List Code) (w : List Bool) :
      (ps.foldl run w).length = w.length + ps.length := by
    induction ps generalizing w with
    | nil => simp
    | cons g ps ih =>
      simp only [List.foldl_cons,ih,run,List.length_append,List.length_cons,List.length_nil]; omega
  have padKeep (ps : List Code) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (ps.foldl run w).getD i false = w.getD i false := by
    induction ps generalizing w with
    | nil => rfl
    | cons g ps ih =>
      rw [List.foldl_cons, ih _ (by simp [run]; omega)]
      exact List.getD_append _ _ _ _ hi
  have gateCount : A.gates.length ≤ 10 := budget
  let padding : List Code := List.replicate (10-A.gates.length) ((0,false),(0,false))
  let program : List.Vector Code 10 := ⟨A.gates.map encode ++ padding, by
    simp only [List.length_append,List.length_map,padding,List.length_replicate]; omega⟩
  let out : Fin 21 := if h : A.output < 10 + A.gates.length then ⟨A.output,by omega⟩ else 20
  have sameOutput (x : Fin 8 → Bool) :
      (program.toList.foldl run (inputs x)).getD out.val false = A.eval (inputs x) := by
    have width : (inputs x).length = 10 := by simp [inputs]
    have hlen : (A.gates.foldl bstep (inputs x)).length = 10 + A.gates.length := by
      rw [wireLen,width]
    change (List.foldl run (inputs x) (A.gates.map encode ++ padding)).getD out.val false =
      (A.gates.foldl bstep (inputs x)).getD A.output false
    rw [List.foldl_append,encList _ (fun _ h => h) _ (by omega)]
    by_cases inside : A.output < 10 + A.gates.length
    · simp only [out,dite_eq_left inside]
      exact padKeep _ _ _ (by omega)
    · simp only [out,dite_eq_right inside]
      rw [List.getD_eq_default _ _ (by rw [padLen,hlen]; simp [padding]; omega),
          List.getD_eq_default _ _ (by omega)]
  obtain ⟨x,miss⟩ := finiteCheck j jchoice program out s
  apply miss
  change ((program.toList.foldl run (inputs x)).getD out.val false != s) = _
  rw [sameOutput]
  exact computesSlice x
