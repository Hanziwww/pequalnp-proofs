import PEqualNP.Defs

-- Project each candidate onto every induced subgraph. Count distinct restricted
-- wire functions after removing constants and primary inputs. The full mask
-- uses the known fifteen-gate bound. The other masks use their exact induced floors.
set_option maxRecDepth 5000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_3869_151
    (pins : let f := fun x : Fin 9 → Bool => ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
    let output := fun (gs : List PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ) (x : Fin 9 → Bool) => let z := (⟨gs,0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x ++ [x 0 || x 3]); z.getD a false || z.getD b false
    ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ), gs.length=13 → PEqualNP.MetaComplexity.FanInTwo ⟨gs,0⟩ →
    (∀ x, output gs a b x=f x) → ∃ j : Fin 12, ∀ x, output gs (10+j.val) 22 x=f x)
    (floors : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D →
    (∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) → let pop := fun (v : ℕ) => (List.range 9).countP (fun j => v.testBit j)
    ∀ m : Fin 512, let u := m.val
    let sig := fun (i : ℕ) (r : Fin 512) => let row : ℕ := r.val
      (D.wires (List.ofFn (fun j : Fin 9 => u.testBit j.val && row.testBit j.val))).getD i false
    let b := if u = 511 then 15 else
      ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).countP (fun e => u.testBit (e / 10) && u.testBit (e % 10)) + pop u -
      (([42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402] : List ℕ).map (fun s => pop (u &&& s))).foldl max 0 - 1
    b ≤ (((Finset.range (9+D.size)).image sig) \ (((Finset.range 9).image sig) ∪
      {fun _ : Fin 512 => false,fun _ : Fin 512 => true})).card)
    (search : let edges : List ℕ := [1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85]
    ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (j : Fin 12),
    let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨⟨.or,[0,3]⟩ :: (gs ++ [⟨.or,[10+j.val,22]⟩]),23⟩
    gs.length=13 → PEqualNP.MetaComplexity.FanInTwo D → gs.countP (fun g => g.op.eval [false]) ≤ 1 →
    (let pop := fun (v : ℕ) => (List.range 9).countP (fun j => v.testBit j)
    ∀ m : Fin 512, let u := m.val
    let sig := fun (i : ℕ) (r : Fin 512) => let row : ℕ := r.val
      (D.wires (List.ofFn (fun j : Fin 9 => u.testBit j.val && row.testBit j.val))).getD i false
    let b := if u = 511 then 15 else
      edges.countP (fun e => u.testBit (e / 10) && u.testBit (e % 10)) + pop u -
      (([42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402] : List ℕ).map (fun s => pop (u &&& s))).foldl max 0 - 1
    b ≤ (((Finset.range (9+D.size)).image sig) \ (((Finset.range 9).image sig) ∪
      {fun _ : Fin 512 => false,fun _ : Fin 512 => true})).card) →
    ∃ x : Fin 9 → Bool, D.eval (List.ofFn x) ≠ edges.any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x1 ≤ (1 : ℕ) →         x2 ≤ (24 : ℕ) →           x3 ≤ (24 : ℕ) →             (∀ x9 ∈ [(0 : ℕ), (3 : ℕ)],                 have x11 : ℕ := List.countP (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => x11.op.eval [Bool.false] && x11.inputs.head? == Option.some x9 || !x11.op.eval [Bool.false] && x11.inputs.contains x9) (x1 ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x2, x3] : PEqualNP.CircuitLowerBounds.Gate }]);                 (1 : ℕ) ≤ x11 ∧ x11 ≤ (2 : ℕ)) →               ∃ (x10 : Fin (9 : ℕ) → Bool),                 have x11 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ))]);                 (x11.getD x2 Bool.false || x11.getD x3 Bool.false) ≠ (x10 (0 : Fin (9 : ℕ)) && x10 (1 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (2 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (3 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (4 : Fin (9 : ℕ)) || x10 (4 : Fin (9 : ℕ)) && x10 (0 : Fin (9 : ℕ)) || x10 (0 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (6 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (5 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (8 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ))) := by
  intro gs a b len fan hn _ _ _
  by_contra! computes
  let f := fun x : Fin 9 → Bool => ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  have truth : ∀ x : Fin 9 → Bool, (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) = f x := by decide +kernel
  have both (x : Fin 9 → Bool) : (let z := (⟨gs,0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x ++ [x 0 || x 3]); z.getD a false || z.getD b false)=f x :=
    (not_ne_iff.mp (computes x)).trans (truth x)
  obtain ⟨j,eq⟩ := pins gs a b len fan both
  let head : PEqualNP.CircuitLowerBounds.Gate := ⟨.or,[0,3]⟩
  let last : PEqualNP.CircuitLowerBounds.Gate := ⟨.or,[10+j.val,22]⟩
  let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨head::(gs++[last]),23⟩
  have hd : PEqualNP.MetaComplexity.FanInTwo D := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl|hg
    · simp [head]
    rcases List.mem_append.mp hg with hg|hg
    · exact fan _ hg
    · obtain rfl := List.mem_singleton.mp hg
      simp [last]
  let step := fun (v : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) => v++[g.op.eval (g.inputs.map fun i => v.getD i false)]
  have length (ds : List PEqualNP.CircuitLowerBounds.Gate) (v : List Bool) : (ds.foldl step v).length=v.length+ds.length := by
    induction ds generalizing v with
    | nil => simp
    | cons g ds ih => rw [List.foldl_cons,ih];simp [step];omega
  have ok (x : Fin 9 → Bool) : D.eval (List.ofFn x)=f x := by
    let v := (List.ofFn x ++ [x 0 || x 3])
    let z := gs.foldl step v
    have start : step (List.ofFn x) head=v := by
      change List.ofFn x ++ [(List.ofFn x).getD 0 false || ((List.ofFn x).getD 3 false || false)] = _
      simp [v,List.getD]
    have hl : z.length=23 := by simp only [z,length,v,List.length_append,List.length_ofFn,List.length_cons,List.length_nil,len]
    change ((gs++[last]).foldl step (step (List.ofFn x) head)).getD 23 false = _
    rw [start,List.foldl_append]
    change (z++[last.op.eval (last.inputs.map fun i => z.getD i false)]).getD 23 false=_
    have atEnd (v : Bool) : (z++[v]).getD 23 false=v := by rw [←hl];simp
    rw [atEnd]
    change PEqualNP.CircuitLowerBounds.GateOp.or.eval [z.getD (10+j.val) false,z.getD 22 false]=_
    calc
      _ = (z.getD (10+j.val) false || z.getD 22 false) := by
        change (_ || (_ || false)) = _
        rw [Bool.or_false]
        rfl
      _ = _ := eq x
  obtain ⟨x,hx⟩ := search gs j len hd hn (floors D hd ok)
  exact hx (ok x)
