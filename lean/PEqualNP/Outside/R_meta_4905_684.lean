import Mathlib.Combinatorics.SimpleGraph.Girth
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4905_684
    (cover : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (T : Finset (Fin n)) (v : Fin n),
      (∀ i j,G.Adj i j → i∈T ∨ j∈T) → v∈T → (∃u w,G.Adj u w ∧ u≠v ∧ w≠v) →
      ∃ s, s+G.degree v+2≤G.edgeFinset.card+T.card ∧
        HasCircuitSize n (fun x => graphFun G ∅ (Function.update x v false)) s)
    (fork : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (v a b : Fin n) (d : Bool),
      let f := graphFun G ∅;
      let W := fun i (x : Fin n→Bool) => (C.wires (List.ofFn x)).getD i false;
      IsMinimalCircuit n C → circuitFun n C=f → 7≤G.egirth → 3≤G.degree v →
      (∃u w,G.Adj u w ∧ u≠v ∧ w≠v) → a≠v → b≠v → a≠b →
      (∃i,∀ x,W i x=(x v && x a)) →
      (∃i,∀ x,W i x=(if d then x v || x b else x v && x b)) → ∃ s, s+4≤C.size ∧ HasCircuitSize n (fun x => f (Function.update x v false)) s)
    (shape : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (v : Fin n),
      IsMinimalCircuit n C → circuitFun n C=graphFun G ∅ → 7≤G.egirth → 3≤G.degree v →
      let W := fun j (x : Fin n→Bool) => (C.wires (List.ofFn x)).getD j false; let r := C.gates.filter (fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val); r.length≤1 →
      ∃ g : Gate, r = [g] ∧ (g.op = GateOp.not ∨ ∃ j ∈ g.inputs, n ≤ j ∧ ∀ (a b : Fin n) (H : Bool→Bool→Bool),
        a≠v → b≠v → (∀ x : Fin n→Bool, W j x=H (x a) (x b)) →
        G.Adj a b ∧ ∀x : Fin n→Bool, W j x=((x a && x b)==g.op.eval [true,false])))
    (remaining : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      let f := graphFun G ∅;
      let r := fun (v : Fin n) => C.gates.filter (fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val);
      let W := fun j (x : Fin n→Bool) => (C.wires (List.ofFn x)).getD j false;
      let h := fun (v j : Fin n) (d : Bool) => ∃ k,∀ x : Fin n→Bool,
        W k x=(if d then x v || x j else x v && x j);
      7≤G.egirth → IsMinimalCircuit n C → circuitFun n C=f →
      (∀ v,G.degree v=0 ∨ G.degree v=3 ∧ (r v).length≤3 ∧ ((r v).length=3 → ∀ g∈r v,g.op=.or)) →
      (∃ (v : Fin n) (g : Gate), G.degree v = 3 ∧ r v = [g] ∧ (g.op = GateOp.not ∨ ∃ j ∈ g.inputs, n ≤ j ∧ ∀ (a b : Fin n) (H : Bool→Bool→Bool),
        a≠v → b≠v → (∀ x : Fin n→Bool, W j x=H (x a) (x b)) →
        G.Adj a b ∧ ∀x : Fin n→Bool, W j x=((x a && x b)==g.op.eval [true,false]))) →
      (∀ T : Finset (Fin n),G.IsVertexCover (T : Set (Fin n)) → C.size+1<G.edgeFinset.card+T.card) →
      (∀ v a b d,G.degree v=3 → a≠v → b≠v → h v a false → h v b d → a=b) →
      ∃ v,G.degree v=3 ∧ ∃ s, s+4≤C.size ∧ HasCircuitSize n (fun x => f (Function.update x v false)) s) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) =>     have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x6.gates;     (∀ x8 ∉ x4, (x7 x8).length ≤ (3 : ℕ) ∧ ((x7 x8).length = (3 : ℕ) → ∀ x11 ∈ x7 x8, x11.op = PEqualNP.CircuitLowerBounds.GateOp.or)) ∧ ∃ x8 ∉ x4, (x7 x8).length ≤ (1 : ℕ);   (∀ x7 ∉ x4, (x2.neighborSet x7).ncard = (3 : ℕ)) → (∀ (x8 : Fin x1) (x9 : x2.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) → (∀ (x9 x10 : Fin x1), x2.Adj x9 x10 → x9 ∉ x4) → (∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11) → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x6 x5 → ∃ x14 ∉ x4, ∃ (x15 : ℕ), x15 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ (Function.update x16 x14 Bool.false)) x15 := by
  intro n G inst A C
  dsimp only
  intro deg girth unmark edge minC compute sparse
  classical
  let f := graphFun G ∅
  let read := fun (v : Fin n) => C.gates.filter (fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)
  let h := fun (v j : Fin n) (d : Bool) => ∃ k,∀ x : Fin n→Bool,
    (C.wires (List.ofFn x)).getD k false=(if d then x v || x j else x v && x j)
  change ( (∀v∉A,(read v).length≤3 ∧ ((read v).length=3 → ∀ g∈read v,g.op=.or)) ∧
    ∃ v∉A,(read v).length≤1 ) at sparse
  have three (v : Fin n) (hv : v∉A) : G.degree v=3 := by rw [←G.ncard_neighborSet];exact deg v hv
  have isolated (v : Fin n) (hv : v∈A) : G.degree v=0 :=
    (G.degree_eq_zero v).mpr (fun w vw => unmark v w vw hv)
  have outside (v : Fin n) (d : G.degree v=3) : v∉A := fun hv => by have := isolated v hv;omega
  have gr : 7≤G.egirth := by
    apply SimpleGraph.le_egirth.mpr;intro v p hp;exact_mod_cast girth v p hp
  have neighbor (v a : Fin n) (hv : v∉A) : ∃ b, G.Adj v b ∧ b≠a := by
    have lt : ({a} : Finset (Fin n)).card<(G.neighborFinset v).card := by
      rw [G.card_neighborFinset_eq_degree,three v hv];simp
    obtain ⟨b,hb,na⟩:=Finset.exists_mem_notMem_of_card_lt_card lt
    exact ⟨b,(G.mem_neighborFinset _ _).mp hb,by simpa using na⟩
  have survives (v : Fin n) (hv : v∉A) : ∃ u w,G.Adj u w ∧ u≠v ∧ w≠v := by
    obtain ⟨u,vu,uv⟩:=neighbor v v hv
    obtain ⟨w,uw,wv⟩:=neighbor u v (unmark u v vu.symm)
    exact ⟨u,w,uw,uv,wv⟩
  by_cases budget : ∃ T : Finset (Fin n),G.IsVertexCover (T:Set (Fin n)) ∧ G.edgeFinset.card+T.card≤C.size+1
  · obtain ⟨T,cov,le⟩:=budget
    obtain ⟨a,b,ab⟩:=edge
    have close (v : Fin n) (vt : v∈T) (va : v∉A) :
        ∃ s,s+4≤C.size ∧ HasCircuitSize n (fun x => f (Function.update x v false)) s := by
      obtain ⟨s,hs,comp⟩:=cover n G T v (fun i j e => cov e) vt (survives v va)
      rw [three v va] at hs
      exact ⟨s,by omega,comp⟩
    rcases cov ab with ta|tb
    · exact ⟨a,unmark a b ab,close a ta (unmark a b ab)⟩
    · exact ⟨b,unmark b a ab.symm,close b tb (unmark b a ab.symm)⟩
  by_cases branches : ∃ v a b d,v∉A ∧ a≠v ∧ b≠v ∧ a≠b ∧ h v a false ∧ h v b d
  · obtain ⟨v,a,b,d,hv,av,bv,ab,ha,hb⟩:=branches
    exact ⟨v,hv,fork n G C v a b d minC compute gr (three v hv).ge (survives v hv) av bv ab ha hb⟩
  obtain ⟨v,hv,once⟩:=sparse.2
  obtain ⟨g,unique,form⟩:=shape n G C v minC compute gr (three v hv).ge once
  obtain ⟨u,du,q,le,hq⟩:=remaining n G C gr minC compute
    (fun i => by by_cases a:i∈A
                 · exact Or.inl (isolated i a)
                 · exact Or.inr ⟨three i a,sparse.1 i a⟩)
    ⟨v,g,three v hv,unique,form⟩
    (fun T cv => Nat.lt_of_not_ge (fun b => budget ⟨T,cv,b⟩))
    (fun i a b d degree av bv ha hb => by by_contra ab;exact branches ⟨i,a,b,d,outside i degree,av,bv,ab,ha,hb⟩)
  exact ⟨u,outside u du,q,le,hq⟩
