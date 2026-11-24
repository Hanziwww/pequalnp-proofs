import Mathlib
import PEqualNP.Defs

-- Petersen vertices are indexed as on the desk. The five maximum independent sets,
-- each stored in ten consecutive bits, have masks 116, 201, 402, 554 and 773.
-- The graph mask records each pair with its smaller index first.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_4077_238
    (geometry : let s := fun (k : Fin 5) (i : Fin 10) => (850517762974836 : ℕ).testBit (10*k.val+i.val)
let strong := fun (h : (Fin 10 → Bool) → Bool) => (∃ a b c : Fin 5,
    a<b ∧ b<c ∧ h (s a)=false ∧ h (s b)=false ∧ h (s c)=false) ∧
    ∀ i : Fin 10, ∃ x : Fin 10 → Bool, x i=false ∧ h x=false ∧ h (Function.update x i true)=true
let goal := fun x : Fin 10 → Bool => decide (∃ a b : Fin 10, a<b ∧ (14321644013157 : ℕ).testBit (b.val*(b.val-1)/2+a.val)=true ∧ x a=true ∧ x b=true)
∀ f g : (Fin 10 → Bool) → Bool, (∀ x, (f x && g x) = goal x) → strong f ∨ strong g)
    (supportBound : ∀ (b : Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C →
  ∀ o : ℕ, ∃ S : Finset (Fin 10), S.card ≤ (o+1-10)+1 ∧ ∀ x y : Fin 10 → Bool, (∀ i∈S, x i=y i) →
    let bank := fun y : Fin 10 → Bool => List.ofFn y ++ [y 0 || if b=true then y 1 else y 2]
    (C.wires (bank x)).getD o false = (C.wires (bank y)).getD o false)
    (leafBound : let star := fun (k : Fin 5) (v : Fin 10) => (850517762974836 : ℕ).testBit (10*k.val+v.val)
let goal := fun x : Fin 10 → Bool => decide (∃ a b : Fin 10, a<b ∧
  (14321644013157 : ℕ).testBit (b.val*(b.val-1)/2+a.val)=true ∧ x a=true ∧ x b=true)
∀ H : (Fin 10 → Bool) → Bool, (∀ x, goal x=true → H x=true) →
  ∀ i j k : Fin 5, i<j → j<k → H (star i)=false → H (star j)=false → H (star k)=false →
  ¬ PEqualNP.MetaComplexity.HasLeafSize 10 H 10)
    (remaining :
    let goal := fun x : Fin 10 → Bool => decide (∃ a b : Fin 10, a<b ∧
      (14321644013157 : ℕ).testBit (b.val*(b.val-1)/2+a.val)=true ∧ x a=true ∧ x b=true)
    let star := fun (k : Fin 5) (i : Fin 10) => (850517762974836 : ℕ).testBit (10*k.val+i.val)
    ∀ (b : Bool) (C : Circuit) (r s : Fin (11+C.size)), FanInTwo C → C.size ≤ 17 → 18 ≤ r.val → 14 ≤ s.val →
      let w := fun (x : Fin 10 → Bool) (k : ℕ) =>
        (C.wires (List.ofFn x ++ [x 0 || if b=true then x 1 else x 2])).getD k false
      (∃ i j k : Fin 5, i<j ∧ j<k ∧ w (star i) r=false ∧ w (star j) r=false ∧ w (star k) r=false) →
      ¬HasLeafSize 10 (fun x => w x r) 10 →
      (∃ x, w x r=true ∧ w x s=false) → (∃ x, w x r=false ∧ w x s=true) →
      ¬(∀ x, (w x r && w x s) = goal x)) :
  ∀ (x1 : Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (17 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → Bool := fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ));       have x8 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x8 : Fin (10 : ℕ) → Bool) (x9 : ℕ) => (x2.wires (List.ofFn x8 ++ [x8 (0 : Fin (10 : ℕ)) || if x1 = Bool.true then x8 (1 : Fin (10 : ℕ)) else x8 (2 : Fin (10 : ℕ))])).getD x9 Bool.false;       (∃ (x9 : Fin (10 : ℕ) → Bool), x8 x9 x3 = Bool.true ∧ x8 x9 x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x8 x10 x3 = Bool.false ∧ x8 x10 x4 = Bool.true) → (∀ (x11 : Fin (10 : ℕ) → Bool), x7 x11 = Bool.true → x8 x11 x3 = Bool.true ∧ x8 x11 x4 = Bool.true) → ∃ (x12 : Fin (10 : ℕ) → Bool), x7 x12 = Bool.false ∧ x8 x12 x3 = Bool.true ∧ x8 x12 x4 = Bool.true := by
  intro flag C u v fan cap F W uv vu on
  let goal := fun x : Fin 10 → Bool => decide (∃ a b : Fin 10, a<b ∧
      (14321644013157 : ℕ).testBit (b.val*(b.val-1)/2+a.val)=true ∧ x a=true ∧ x b=true)
  let star := fun (k : Fin 5) (i : Fin 10) => (850517762974836 : ℕ).testBit (10*k.val+i.val)
  have meaning : ∀ x, goal x = F x := by decide +kernel
  by_contra no
  have prod (x : Fin 10 → Bool) : (W x u && W x v)=goal x := by
    rw [meaning]
    cases positive : F x with
    | true => exact Bool.and_eq_true_iff.mpr (on x positive)
    | false =>
      apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨hu,hv⟩ := Bool.and_eq_true_iff.mp h
      exact no ⟨x,positive,hu,hv⟩
  have heavy (r : ℕ) (essential : ∀ i : Fin 10, ∃ x : Fin 10 → Bool,
        x i=false ∧ W x r=false ∧ W (Function.update x i true) r=true) : 18≤r := by
    obtain ⟨S,cost,same⟩ := supportBound flag C fan r
    have full (i : Fin 10) : i∈S := by
      by_contra absent
      obtain ⟨x,_,low,high⟩ := essential i
      have eq := same x (Function.update x i true) (by
        intro j hj
        exact (Function.update_of_ne (show j≠i from fun h => absent (h ▸ hj)) ..).symm)
      change W x r = W (Function.update x i true) r at eq
      rw [low,high] at eq
      contradiction
    have large := Finset.card_le_card (show (Finset.univ : Finset (Fin 10)) ⊆ S from fun i _ => full i)
    simp only [Finset.card_univ,Fintype.card_fin] at large
    omega
  have light (r : ℕ) (covers : ∀ x, F x=true → W x r=true)
      (misses : ∃ x, W x r=false) : 14≤r := by
    by_contra! early
    obtain ⟨S,cost,same⟩ := supportBound flag C fan r
    have sparse := (show ∀ T : Finset (Fin 10), T.card≤5 → ∃ a b : Fin 10, a<b ∧
        (14321644013157 : ℕ).testBit (b.val*(b.val-1)/2+a.val)=true ∧ a∉T ∧ b∉T from by decide +kernel)
    obtain ⟨a,b,ab,edge,ha,hb⟩ := sparse S (by omega)
    obtain ⟨x,hx⟩ := misses
    let y (i : Fin 10) := if i∈S then x i else true
    have positive : goal y=true := decide_eq_true ⟨a,b,ab,edge,by simp [y,ha],by simp [y,hb]⟩
    have eq := same x y (fun i hi => by simp [y,hi])
    change W x r=W y r at eq
    rw [hx,covers y ((meaning y).symm.trans positive)] at eq
    contradiction
  have lightU : 14≤u := light u (fun x h => (on x h).1) (by obtain ⟨x,h,_⟩ := vu;exact ⟨x,h⟩)
  have lightV : 14≤v := light v (fun x h => (on x h).2) (by obtain ⟨x,_,h⟩ := uv;exact ⟨x,h⟩)
  have lengthLaw (gs : List Gate) (w : List Bool) :
      (gs.foldl (fun (z : List Bool) (g : Gate) => z ++ [g.op.eval (g.inputs.map fun i => z.getD i false)]) w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => simp only [List.foldl_cons,ih,List.length_append,List.length_cons,List.length_nil];omega
  have valid (r : ℕ) (value : ∃ x : Fin 10 → Bool, W x r=true) : r<11+C.size := by
    by_contra! beyond
    obtain ⟨x,hx⟩ := value
    let initial := List.ofFn x ++ [x 0 || if flag=true then x 1 else x 2]
    change (C.wires initial).getD r false = true at hx
    have len : (C.wires initial).length=11+C.size := by
      change (C.gates.foldl (fun (z : List Bool) (g : Gate) => z ++ [g.op.eval (g.inputs.map fun i => z.getD i false)]) initial).length=11+C.gates.length
      rw [lengthLaw]
      simp [initial]
    rw [List.getD_eq_default _ false (by omega)] at hx
    contradiction
  have gu := valid u (by obtain ⟨x,h,_⟩ := uv;exact ⟨x,h⟩)
  have gv := valid v (by obtain ⟨x,_,h⟩ := vu;exact ⟨x,h⟩)
  have formulaCost (r : ℕ) (hits : ∀ x, F x=true → W x r=true)
      (witness : ∃ a b c : Fin 5, a<b ∧ b<c ∧ W (star a) r=false ∧ W (star b) r=false ∧ W (star c) r=false) :
      ¬ HasLeafSize 10 (fun x => W x r) 10 := by
    obtain ⟨a,b,c,ab,bc,ha,hb,hc⟩ := witness
    exact leafBound _ (fun x h => hits x ((meaning x).symm.trans h)) a b c ab bc ha hb hc
  rcases geometry (fun x => W x u) (fun x => W x v) prod with h|h
  · exact (remaining flag C ⟨u,gu⟩ ⟨v,gv⟩ fan cap (heavy u h.2) lightV h.1 (formulaCost u (fun x e => (on x e).1) h.1) uv vu) prod
  · apply (remaining flag C ⟨v,gv⟩ ⟨u,gu⟩ fan cap (heavy v h.2) lightU h.1 (formulaCost v (fun x e => (on x e).2) h.1))
    · obtain ⟨x,hu,hv⟩ := vu
      exact ⟨x,hv,hu⟩
    · obtain ⟨x,hu,hv⟩ := uv
      exact ⟨x,hv,hu⟩
    · intro x
      rw [Bool.and_comm]
      exact prod x
