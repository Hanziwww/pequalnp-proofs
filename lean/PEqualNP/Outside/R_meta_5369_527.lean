import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_5369_527
    (limits :
    let I := fun (x : Fin 10→Bool) => List.ofFn x ++ [!x 0];
    let F := fun (x : Fin 10→Bool) => (List.finRange 5).any fun i =>
       x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i+1)) ||
       x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i) ||
       x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i+2));
    ∀ D : Circuit,FanInTwo D → (∀x,D.eval (I x)=F x) →
    let W := fun (j : ℕ) (x : Fin 10→Bool) => (D.wires (I x)).getD j false;
    (∀(b : Bool) (K : Finset ℕ),(∀j∈K,j<D.size ∧ ∃i<11+j,∀x : Fin 10→Bool,x 0=b → W (11+j) x=W i x) → (if b then 11 else 16)+K.card≤D.size) ∧
    ((∀g∈D.gates,g.op=GateOp.not → g.inputs.length≤1) → D.size≤18 → D.gates.countP (fun (g : Gate) => g.inputs.contains 0 || g.inputs.contains 10)=2 →
      ∀j : Fin D.gates.length,(∃i<11+j.val,∀x : Fin 10→Bool,x 0=false → W (11+j.val) x=W i x) → (¬(∃v : Bool,∀x : Fin 10→Bool,x 0=false → W (11+j.val) x=v)) →
      let g := D.gates.get j; (g.op=GateOp.or ∧ 0∈g.inputs ∧ 10∉g.inputs) ∨ (g.op=GateOp.and ∧ 10∈g.inputs ∧ 0∉g.inputs)))
    (selectCircuit :
    let I := fun (x : Fin 10→Bool) => List.ofFn x ++ [!x 0];
    let F := fun (x : Fin 10→Bool) => (List.finRange 5).any fun i =>
       x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i+1)) ||
       x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i) ||
       x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i+2));
    let S := fun (D : Circuit) => FanInTwo D ∧ ∀x,D.eval (I x)=F x;
    let R := fun (g : Gate) => g.inputs.contains 0 || g.inputs.contains 10;
    (∃C : Circuit,S C ∧ C.size≤18) → ∃D : Circuit,S D ∧ D.size≤18 ∧
      (let r := D.gates.countP R;
       let W := fun (j : ℕ) (x : Fin 10→Bool) => (D.wires (I x)).getD j false;
       0<r ∧ 16+r≤D.size ∧ (D.size=17 → ∃g∈D.gates,g.op=GateOp.and ∧ 10∈g.inputs) ∧
       (∀g∈D.gates,g.op=GateOp.not → g.inputs.length≤1) ∧
       ∀j : Fin D.gates.length,(∃v : Bool,∀x : Fin 10→Bool,x 0=false → W (11+j.val) x=v) →
         R (D.gates.get j)=true ∧ r=1 ∧ D.size=18 ∧ (∃! k : Fin D.gates.length,j<k ∧ 11+j.val∈(D.gates.get k).inputs)))
    (oneReader :
    let I := fun (x : Fin 10→Bool) => List.ofFn x ++ [!x 0];
    let F := fun (x : Fin 10→Bool) => (List.finRange 5).any fun i =>
       x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i+1)) ||
       x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i) ||
       x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i+2));
    let R := fun (g : Gate) => g.inputs.contains 0 || g.inputs.contains 10; ∀ D : Circuit,let r := D.gates.countP R;
    let W := fun (j : ℕ) (x : Fin 10→Bool) => (D.wires (I x)).getD j false;
    FanInTwo D → 17≤D.size → D.size≤18 → r=1 → (D.size=17 → ∃g∈D.gates,g.op=GateOp.and ∧ 10∈g.inputs) → (∀g∈D.gates,g.op=GateOp.not → g.inputs.length≤1) →
    (∀j : Fin D.gates.length,(∃v : Bool,∀x : Fin 10→Bool,x 0=false → W (11+j.val) x=v) → R (D.gates.get j)=true ∧ D.size=18 ∧ (∃! k : Fin D.gates.length,j<k ∧ 11+j.val∈(D.gates.get k).inputs)) →
    (∀(b : Bool) (K : Finset ℕ),(∀j∈K,j<D.size ∧ ∃i<11+j,∀x : Fin 10→Bool,x 0=b → W (11+j) x=W i x) → (if b then 11 else 16)+K.card≤D.size) → ∃x,D.eval (I x)≠F x)
    (twoReaders :
    let I := fun (x : Fin 10→Bool) => List.ofFn x ++ [!x 0];
    let F := fun (x : Fin 10→Bool) => (List.finRange 5).any fun i =>
       x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i+1)) ||
       x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i) ||
       x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i+2));
    ∀ D : Circuit,
    let W := fun (j : ℕ) (x : Fin 10→Bool) => (D.wires (I x)).getD j false;
    FanInTwo D → D.size=18 → D.gates.countP (fun (g : Gate) => g.inputs.contains 0 || g.inputs.contains 10)=2 → (∀g∈D.gates,g.op=GateOp.not → g.inputs.length≤1) →
    (∀j : Fin D.gates.length,¬(∃v : Bool,∀x : Fin 10→Bool,x 0=false → W (11+j.val) x=v)) → (∀j : Fin D.gates.length,(∃i<11+j.val,∀x : Fin 10→Bool,x 0=false → W (11+j.val) x=W i x) → let g := D.gates.get j; (g.op=GateOp.or ∧ 0∈g.inputs ∧ 10∉g.inputs) ∨ (g.op=GateOp.and ∧ 10∈g.inputs ∧ 0∉g.inputs)) →
    (∀(b : Bool) (K : Finset ℕ),(∀j∈K,j<D.size ∧ ∃i<11+j,∀x : Fin 10→Bool,x 0=b → W (11+j) x=W i x) → (if b then 11 else 16)+K.card≤D.size) → ∃x,D.eval (I x)≠F x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (18 : ℕ) →       List.countP             (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) =>               have x5 : List ℕ := PEqualNP.CircuitLowerBounds.GateOp.rec x4.inputs x4.inputs (List.take (1 : ℕ) x4.inputs) (fun (x5 : ℕ) => x4.inputs) x4.inputs x4.op;               x5.contains (0 : ℕ) || x5.contains (10 : ℕ))             x1.gates ≤           (3 : ℕ) →         ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [!x5 (0 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5 := by
  classical
  let I := fun (x : Fin 10→Bool) => List.ofFn x ++ [!x 0]
  let F := fun (x : Fin 10→Bool) => (List.finRange 5).any fun i =>
       x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i+1)) ||
       x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i) ||
       x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i+2))
  let P := fun (x : Fin 10→Bool) =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  have same : ∀x,F x=P x := by decide +kernel
  intro C fan size _read
  change ∃x,C.eval (I x)≠P x
  by_contra! good
  have correct : ∀x,C.eval (I x)=F x := fun x => (good x).trans (same x).symm
  obtain ⟨D,works,cap,pos,spent,negative,normal,cut⟩:=selectCircuit ⟨C,⟨fan,correct⟩,size⟩
  let R := fun (g : Gate) => g.inputs.contains 0 || g.inputs.contains 10
  let r := D.gates.countP R
  change 0<r at pos
  change 16+r≤D.size at spent
  have bounds:=limits D works.1 works.2
  have bad : ∃x,D.eval (I x)≠F x := by
    by_cases m : r=1
    · exact oneReader D works.1 (by omega) cap m negative normal
        (fun j h => ⟨(cut j h).1,(cut j h).2.2⟩) bounds.1
    · have t : r=2 := by omega
      have nc := fun j h => m (cut j h).2.1
      exact twoReaders D works.1 (by omega) t normal nc
        (fun j rep => bounds.2 normal cap t j rep (nc j)) bounds.1
  obtain ⟨x,hx⟩:=bad
  exact hx (works.2 x)
