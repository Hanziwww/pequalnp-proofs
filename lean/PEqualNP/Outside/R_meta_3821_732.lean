import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_3821_732
    (pin : let G := fun (x : Fin 10 → Bool) => (List.finRange 5).any fun i => x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i+1)) || x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i) || x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i+2));
    ∀ (D : Circuit) (i : Fin 10) (J : Finset (Fin 10)),
      FanInTwo D → i∉J → D.size≤17+J.card →
      (∀ j∈J, ∃ n, ∀ x : Fin 10 → Bool,
        (D.wires (List.ofFn x)).getD n false = (x i && x j)) →
      (∀ x : Fin 10 → Bool, G x=false ∨ (List.ofFn x).count true≤2 → circuitFun 10 D x=G x) →
      ∃ p : Equiv.Perm (Fin 10), (∀ x, G (x ∘ p)=G x) ∧
        HasCircuitSize 9 (fun y => circuitFun 10 D (Fin.lastCases false y ∘ p)) 15)
    (ends : let G := fun (x : Fin 10 → Bool) => (List.finRange 5).any fun i => x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i+1)) || x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i) || x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i+2));
    ∀ (f g : (Fin 10 → Bool) → Bool),
      (∀ i j : Fin 10, let x := fun k : Fin 10 => decide (k=i ∨ k=j); (f x || g x)=G x) →
      let c := fun H : (Fin 10 → Bool) → Bool => (List.finRange 10).countP fun i => (List.finRange 10).any fun j => H (fun k => decide (k=i ∨ k=j));
      let r := max (c f) (c g); 10≤r ∨ 22≤c f+c g+r)
    (remaining : let G := fun (x : Fin 10 → Bool) => (List.finRange 5).any fun i => x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i+1)) || x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i) || x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i+2));
    ∀ (D : Circuit) (a b : ℕ), FanInTwo D → D.size≤19 →
      D.gates.getLast?=some ⟨.or,[a,b]⟩ → D.output+1=10+D.size →
      let W := fun (n : ℕ) (x : Fin 10 → Bool) => (D.wires (List.ofFn x)).getD n false;
      let F := W D.output;
      (¬ W a ≤ W b) → (¬ W b ≤ W a) →
      (∀ x : Fin 10 → Bool, G x=false ∨ (List.ofFn x).count true≤2 → F x=G x) →
      (∀ (i : Fin 10) (J : Finset (Fin 10)), i∉J →
        (∀ j∈J, ∃ n, ∀ x, W n x=(x i && x j)) → 17+J.card<D.size) →
      let c := fun n : ℕ => (List.finRange 10).countP fun i => (List.finRange 10).any fun j => W n (fun k => decide (k=i ∨ k=j));
      let r := max (c a) (c b); (10≤r ∨ 22≤c a+c b+r) →
      ∃ (p : Equiv.Perm (Fin 10)) (v : Bool), (∀ x, G (x ∘ p)=G x) ∧
        HasCircuitSize 9 (fun y => F (Fin.lastCases v y ∘ p)) (if v then 10 else 15)) :
    have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ)))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (18 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x7 : Fin (10 : ℕ) → Bool) (x8 : ℕ) => (x2.wires (List.ofFn x7)).getD x8 Bool.false;       have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x7 x8 x3 || x7 x8 x4;       (∃ (x9 : Fin (10 : ℕ) → Bool), x7 x9 x3 = Bool.true ∧ x7 x9 x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x7 x10 x3 = Bool.false ∧ x7 x10 x4 = Bool.true) → (∀ (x11 : Fin (10 : ℕ) → Bool), x1 x11 = Bool.false ∨ List.count Bool.true (List.ofFn x11) ≤ (2 : ℕ) → x8 x11 = x1 x11) → ∃ (x12 : Equiv.Perm (Fin (10 : ℕ))) (x13 : Bool) (x14 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x15 : Fin (10 : ℕ) → Bool), x1 (x15 ∘ ⇑x12) = x1 x15) ∧ PEqualNP.MetaComplexity.FanInTwo x14 ∧ (x14.size ≤ if x13 = Bool.true then (10 : ℕ) else (15 : ℕ)) ∧ ∀ (x15 : Fin (9 : ℕ) → Bool), x14.eval (List.ofFn x15) = x8 ((fun (x16 : Fin ((9 : ℕ) + (1 : ℕ))) => Fin.lastCases x13 x15 x16) ∘ ⇑x12) := by
  classical
  dsimp only
  intro C a b fan sz
  let G := fun (x : Fin 10 → Bool) => (List.finRange 5).any fun i => x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i+1)) || x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i) || x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i+2))
  let W := fun (n : ℕ) (x : Fin 10 → Bool) => (C.wires (List.ofFn x)).getD n false
  let U := fun x => W a x || W b x
  intro ha hb rows
  let last : Gate := ⟨.or,[a,b]⟩
  let D : Circuit := ⟨C.gates++[last],10+C.size⟩
  have length (gs : List Gate) (v : List Bool) :
      (gs.foldl (fun p (g : Gate) => p++[g.op.eval (g.inputs.map fun i => p.getD i false)]) v).length=v.length+gs.length := by
    induction gs generalizing v with
    | nil => simp
    | cons g gs ih => simp only [List.foldl_cons];rw [ih];simp;omega
  have len (x : Fin 10 → Bool) : (C.wires (List.ofFn x)).length=10+C.size := by
    have h := length C.gates (List.ofFn x)
    rw [List.length_ofFn] at h
    exact h
  have tapes (x : Fin 10 → Bool) : D.wires (List.ofFn x)=C.wires (List.ofFn x)++[U x] := by
    let step := fun (l : List Bool) (g : Gate) => l++[g.op.eval (g.inputs.map fun i => l.getD i false)]
    change (C.gates++[last]).foldl step (List.ofFn x)=_
    rw [List.foldl_append]
    change C.wires (List.ofFn x)++[GateOp.or.eval [W a x,W b x]]=
      C.wires (List.ofFn x)++[W a x || W b x]
    cases W a x <;> cases W b x <;> rfl
  have output (x : Fin 10 → Bool) : circuitFun 10 D x=U x := by
    change (D.wires (List.ofFn x)).getD (10+C.size) false=_
    rw [tapes,←len x];simp
  have fD : FanInTwo D := by
    intro g hm
    change g∈C.gates++[last] at hm
    rcases List.mem_append.mp hm with h|h
    · exact fan _ h
    · obtain rfl := List.mem_singleton.mp h
      simp [last]
  have ds : D.size=C.size+1 := by change (C.gates++[last]).length=C.gates.length+1;simp
  have rd : ∀ x : Fin 10 → Bool, G x=false ∨ (List.ofFn x).count true≤2 → circuitFun 10 D x=G x :=
    fun x hx => (output x).trans (rows x hx)
  have bounds (n : ℕ) {x : Fin 10 → Bool} (h : W n x=true) : n<10+C.size := by
    by_contra! bad
    have no : (C.wires (List.ofFn x)).length≤n := (len x) ▸ bad
    change (C.wires (List.ofFn x)).getD n false=true at h
    rw [List.getD_eq_default _ _ no] at h
    exact Bool.noConfusion h
  have old (n : ℕ) (h : n<10+C.size) (x : Fin 10 → Bool) :
      (D.wires (List.ofFn x)).getD n false=W n x := by
    rw [tapes]; exact List.getD_append _ _ _ _ (by rwa [len])
  let WD := fun (n : ℕ) (x : Fin 10 → Bool) => (D.wires (List.ofFn x)).getD n false
  have both : (¬ WD a ≤ WD b) ∧ (¬ WD b ≤ WD a) := by
    obtain ⟨x,ax,bx⟩ := ha
    obtain ⟨y,ay,by'⟩ := hb
    change W a x=true at ax
    change W b x=false at bx
    change W a y=false at ay
    change W b y=true at by'
    constructor
    · intro h
      have bad := h x
      change (D.wires (List.ofFn x)).getD a false ≤ (D.wires (List.ofFn x)).getD b false at bad
      rw [old a (bounds a ax),old b (bounds b by'),ax,bx] at bad
      exact (by decide : ¬ true≤false) bad
    · intro h
      have bad := h y
      change (D.wires (List.ofFn y)).getD b false ≤ (D.wires (List.ofFn y)).getD a false at bad
      rw [old b (bounds b by'),old a (bounds a ax),by',ay] at bad
      exact (by decide : ¬ true≤false) bad
  let appears := fun (i j : Fin 10) => ∃ n, ∀ x : Fin 10 → Bool,
    (D.wires (List.ofFn x)).getD n false=(x i && x j)
  have result : ∃ (p : Equiv.Perm (Fin 10)) (v : Bool), (∀ x,G (x ∘ p)=G x) ∧
      HasCircuitSize 9 (fun y => circuitFun 10 D (Fin.lastCases v y ∘ p)) (if v then 10 else 15) := by
    by_cases h : ∃ (i : Fin 10) (J : Finset (Fin 10)), i∉J ∧ D.size≤17+J.card ∧ ∀ j∈J, appears i j
    · obtain ⟨i,J,hn,le,ev⟩ := h
      obtain ⟨p,aut,comp⟩ := pin D i J fD hn le ev rd
      exact ⟨p,false,aut,comp⟩
    · apply remaining D a b fD (by omega) (by simp [D,last]) (by change 10+C.size+1=10+D.size;omega) both.1 both.2 rd
      · intro i J hn ev
        exact Nat.lt_of_not_ge fun le => h ⟨i,J,hn,le,ev⟩
      · apply ends (fun x => (D.wires (List.ofFn x)).getD a false) (fun x => (D.wires (List.ofFn x)).getD b false)
        intro i j
        obtain ⟨x0,yesA,_⟩ := ha
        obtain ⟨x1,_,yesB⟩ := hb
        let x := fun k : Fin 10 => decide (k=i ∨ k=j)
        change ((D.wires (List.ofFn x)).getD a false || (D.wires (List.ofFn x)).getD b false)=G x
        rw [old a (bounds a yesA),old b (bounds b yesB)]
        have two : ∀ u v : Fin 10, (List.ofFn (fun k : Fin 10 => decide (k=u ∨ k=v))).count true≤2 := by decide +kernel
        exact rows x (Or.inr (two i j))
  obtain ⟨p,v,aut,B,hB,size,sim⟩ := result
  exact ⟨p,v,B,aut,hB,by simpa using size,fun y => (sim y).trans (output _)⟩
