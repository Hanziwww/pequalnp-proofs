import Mathlib
import PEqualNP.Defs

-- The positive rows are the fifteen edges and the negative rows the maximal independent sets.
-- The open steps isolate removal of negations and the cost of shared monotone gates.
-- The 21-rectangle lower bound is proved here by integer weights and a parity certificate.
-- The cyclic labeling argument follows the reduction R_meta_2373_71 by AidenCB.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_2373_73
    (helim : let G := (fun x : Fin 10 → Bool => (List.finRange 5).any fun i =>
        (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
        (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
        (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2))))
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D →
        (∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = G x) →
        ∃ M : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 M ∧
          M.size ≤ D.size ∧ ∀ x : Fin 10 → Bool, M.eval (List.ofFn x) = G x)
    (hpart : let P := fun (r : Fin 15) (v : Fin 10) => (401849741469506565305680851550143442694707203 : ℕ).testBit (10*r.val+v.val)
      let N := fun (r : Fin 15) (v : Fin 10) => (1078453559198442499535953780770134430129919026 : ℕ).testBit (10*r.val+v.val)
      ∀ M : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 M →
        (∀ r, M.eval (List.ofFn (P r)) = true) → (∀ s, M.eval (List.ofFn (N s)) = false) →
        ∃ T : List (Finset (Fin 15) × Finset (Fin 15)), T.length ≤ M.size+1 ∧
          (∀ t ∈ T, ∃ v : Fin 10, (∀ r ∈ t.1, P r v = true) ∧ (∀ s ∈ t.2, N s v = false)) ∧ (∀ r s : Fin 15, (T.filter (fun t => decide (r ∈ t.1 ∧ s ∈ t.2))).length = 1)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false := by
  let inputColumns : List ℕ := [579928113, 419987523, 608501894, 169476364, 23364120, 201770016, 3616832, 28839040, 834691328, 1040194048]
  let starting (i : Fin 10) := inputColumns.getD i.val 0
  -- Each nibble stores an integer weight plus four. The second mask marks 47 cells.
  let weightDigits : List ℕ := [605794099899269956, 605843565834437446, 592335515202913891, 15820337124378166, 590029303035691876, 592335519229380196, 20322836971685446, 590045795710174051, 605794100167705651, 605844665362776886, 15836833825326646, 605811692102091571, 596839114578560611, 594531803151434851, 605843570129339446]
  let weight (p q : (Fin 15)) : ℤ :=
    Int.ofNat (((weightDigits.getD p.val 0) >>> (4*q.val)) % 16) - 4
  let colour (p q : (Fin 15)) : ℤ :=
    if (0x15384bb0970d8f1913b01449020801048020100000000000000000000 : ℕ).testBit (15*p.val+q.val) then 1 else 0
  let yes (w : ℕ) : Finset (Fin 15) := Finset.univ.filter fun p => w.testBit p.val
  let no (w : ℕ) : Finset (Fin 15) := Finset.univ.filter fun q => !(w.testBit (q.val+15))
  let rowSum (m : (Fin 15) → (Fin 15) → ℤ) (A : Finset (Fin 15)) (j : (Fin 15)) := ∑ i ∈ A, m i j
  let box (m : (Fin 15) → (Fin 15) → ℤ) (A B : Finset (Fin 15)) := ∑ j ∈ B, rowSum m A j
  let rectangle (A B : Finset (Fin 15)) := box weight A B + box colour A B % 2
  let pick (w : ℤ × ℤ) (p : ℤ) : ℤ := if p % 2 = 0 then w.1 else w.2
  -- The two entries maximize the attainable score for each incoming parity.
  let bounds (v c : (Fin 15) → ℤ) (l : List (Fin 15)) : ℤ × ℤ := l.foldr (fun j b =>
      (max b.1 (v j + pick b (c j)), max b.2 (v j + pick b (1+c j)))) (0,1)
  have take_step (v c : (Fin 15) → ℤ) (j : (Fin 15)) (rest : List (Fin 15)) (p : ℤ) :
      pick (bounds v c (j::rest)) p =
        max (pick (bounds v c rest) p) (v j + pick (bounds v c rest) (p+c j)) := by
    simp only [bounds,List.foldr_cons,pick]
    split_ifs <;> first | rfl | omega
  have every_subset (v c : (Fin 15) → ℤ) (l : List (Fin 15)) (B : Finset (Fin 15)) (p : ℤ)
      (sub : ∀ j ∈ B, j ∈ l) :
      (∑ j ∈ B, v j) + (p + ∑ j ∈ B, c j) % 2 ≤ pick (bounds v c l) p := by
    induction l generalizing B p with
    | nil =>
      have e : B = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro j hj
        exact List.not_mem_nil (sub j hj)
      rw [e]
      simp only [Finset.sum_empty,Int.add_zero,Int.zero_add,bounds,List.foldr_nil,pick]
      split <;> omega
    | cons j l ih =>
      rw [take_step]
      by_cases mem : j ∈ B
      · have small : ∀ k ∈ B.erase j, k ∈ l := by
          intro k hk
          obtain ⟨ne,hB⟩ := Finset.mem_erase.mp hk
          exact (List.mem_cons.mp (sub k hB)).resolve_left ne
        have vr := Finset.add_sum_erase B v mem
        have cr := Finset.add_sum_erase B c mem
        have ind := ih (B.erase j) (p+c j) small
        apply le_trans _ (le_max_right _ _)
        rw [← vr, ← cr, ← add_assoc p]
        omega
      · have small : ∀ k ∈ B, k ∈ l := by
          intro k hk
          exact (List.mem_cons.mp (sub k hk)).resolve_left (fun h => mem (h ▸ hk))
        exact (ih B p small).trans (le_max_left _ _)
  let positiveList (i : Fin 10) := (List.finRange 15).filter (fun p => (starting i).testBit p.val)
  let negativeList (i : Fin 10) := (List.finRange 15).filter (fun q => !((starting i).testBit (q.val+15)))
  let checkLiteral (i : Fin 10) : Bool :=
    (positiveList i).sublists.all fun a =>
      decide (pick (bounds (rowSum weight a.toFinset) (rowSum colour a.toFinset) (negativeList i)) 0 ≤ 12)
  have all_literal_checks : ∀ i : Fin 10, checkLiteral i = true := by decide +kernel
  have raw_bound (i : Fin 10) (A B : Finset (Fin 15)) (hA : A ⊆ yes (starting i)) (hB : B ⊆ no (starting i)) :
      rectangle A B ≤ 12 := by
    let L := (positiveList i).filter (fun p => p∈A)
    have sub : L.Sublist (positiveList i) := List.filter_sublist
    have eq : L.toFinset = A := by
      ext p
      simp only [L,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,positiveList,List.mem_finRange,true_and]
      exact and_iff_right_of_imp (fun hp => (Finset.mem_filter.mp (hA hp)).2)
    have all := all_literal_checks i
    change (positiveList i).sublists.all _ = true at all
    have ok := of_decide_eq_true (List.all_eq_true.mp all L (List.mem_sublists.mpr sub))
    rw [eq] at ok
    apply le_trans _ ok
    have q := every_subset (rowSum weight A) (rowSum colour A) (negativeList i) B 0 (by
      intro j hj
      exact List.mem_filter.mpr ⟨List.mem_finRange _, (Finset.mem_filter.mp (hB hj)).2⟩)
    simpa only [rectangle,box,Int.zero_add] using q
  have total_score : rectangle Finset.univ Finset.univ = 241 := by decide +kernel
  have parity_subadditive (a b : ℤ) : (a+b)%2 ≤ a%2+b%2 := by omega
  let contains (t : (Finset (Fin 15) × Finset (Fin 15))) (p q : (Fin 15)) : ℕ := if p∈t.1 ∧ q∈t.2 then 1 else 0
  let multiplicity (T : List (Finset (Fin 15) × Finset (Fin 15))) (p q : (Fin 15)) := (T.map fun t => contains t p q).sum
  have box_all (m : (Fin 15) → (Fin 15) → ℤ) (t : (Finset (Fin 15) × Finset (Fin 15))) :
      box m t.1 t.2 = ∑ q : (Fin 15), ∑ p : (Fin 15), (contains t p q:ℤ)*m p q := by
    unfold box rowSum contains
    simp only [apply_ite Nat.cast,Nat.cast_one,Nat.cast_zero,ite_mul,one_mul,zero_mul]
    calc
      _ = ∑ q : (Fin 15), if q ∈ t.2 then ∑ p ∈ t.1, m p q else 0 := by simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro q _
        by_cases h : q ∈ t.2 <;> simp [h]
  have add_boxes (m : (Fin 15) → (Fin 15) → ℤ) (T : List (Finset (Fin 15) × Finset (Fin 15))) :
      (T.map fun t => box m t.1 t.2).sum =
        ∑ q : (Fin 15), ∑ p : (Fin 15), (multiplicity T p q:ℤ)*m p q := by
    induction T with
    | nil => simp [multiplicity]
    | cons t T ih =>
      simp only [List.map_cons,List.sum_cons,ih,box_all m t,multiplicity,Nat.cast_add,add_mul,
        Finset.sum_add_distrib]
  -- The whole matrix scores 241. A literal rectangle scores at most 12.
  have partition_lower (T : List (Finset (Fin 15) × Finset (Fin 15)))
      (literal : ∀ t ∈ T, ∃ i : Fin 10, t.1 ⊆ yes (starting i) ∧ t.2 ⊆ no (starting i))
      (covers : ∀ p q, multiplicity T p q = 1) : 21 ≤ T.length := by
    have full (m : (Fin 15) → (Fin 15) → ℤ) :
        (T.map fun t => box m t.1 t.2).sum = box m Finset.univ Finset.univ := by
      rw [add_boxes]
      simp only [covers,Nat.cast_one,one_mul,box,rowSum]
    have add_scores (S : List (Finset (Fin 15) × Finset (Fin 15))) :
        (S.map fun t => box weight t.1 t.2).sum + (S.map fun t => box colour t.1 t.2).sum%2 ≤
          (S.map fun t => rectangle t.1 t.2).sum := by
      induction S with
      | nil => decide
      | cons t S ih =>
        simp only [List.map_cons,List.sum_cons]
        have h := parity_subadditive (box colour t.1 t.2) ((S.map fun u => box colour u.1 u.2).sum)
        unfold rectangle at ih ⊢
        omega
    have at_most (S : List (Finset (Fin 15) × Finset (Fin 15)))
        (h : ∀ t ∈ S, rectangle t.1 t.2 ≤ 12) :
        (S.map fun t => rectangle t.1 t.2).sum ≤ 12*(S.length:ℤ) := by
      induction S with
      | nil => simp
      | cons t S ih =>
        have first := h t List.mem_cons_self
        have rest := ih (fun u hu => h u (List.mem_cons_of_mem t hu))
        simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
        omega
    have bound := at_most T (fun t ht => by
      obtain ⟨i,ha,hb⟩ := literal t ht
      exact raw_bound i t.1 t.2 ha hb)
    have h := add_scores T
    rw [full weight,full colour] at h
    have total := total_score
    unfold rectangle at total
    omega
  have hrect : let P := fun (r : Fin 15) (v : Fin 10) => (401849741469506565305680851550143442694707203 : ℕ).testBit (10*r.val+v.val)
        let N := fun (r : Fin 15) (v : Fin 10) => (1078453559198442499535953780770134430129919026 : ℕ).testBit (10*r.val+v.val)
        ∀ T : List (Finset (Fin 15) × Finset (Fin 15)), (∀ t ∈ T, ∃ v : Fin 10, (∀ r ∈ t.1, P r v = true) ∧ (∀ s ∈ t.2, N s v = false)) →
          (∀ r s : Fin 15, (T.filter (fun t => decide (r ∈ t.1 ∧ s ∈ t.2))).length = 1) → 21 ≤ T.length := by
    let P := fun (r : Fin 15) (v : Fin 10) => (401849741469506565305680851550143442694707203 : ℕ).testBit (10*r.val+v.val)
    let N := fun (r : Fin 15) (v : Fin 10) => (1078453559198442499535953780770134430129919026 : ℕ).testBit (10*r.val+v.val)
    change ∀ T : List (Finset (Fin 15) × Finset (Fin 15)), (∀ t ∈ T, ∃ v : Fin 10, (∀ r ∈ t.1, P r v = true) ∧ (∀ s ∈ t.2, N s v = false)) →
      (∀ r s : (Fin 15), (T.filter (fun t => decide (r∈t.1 ∧ s∈t.2))).length = 1) → 21 ≤ T.length
    have rawP : ∀ (r : (Fin 15)) (v : Fin 10), P r v = (starting v).testBit r.val := by decide +kernel
    have rawN : ∀ (s : (Fin 15)) (v : Fin 10), N s v = (starting v).testBit (s.val+15) := by decide +kernel
    intro T lit unique
    apply partition_lower T
    · intro t ht
      obtain ⟨v,hp,hn⟩ := lit t ht
      refine ⟨v,?_,?_⟩
      · intro r hr
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (rawP r v).symm.trans (hp r hr)⟩
      · intro s hs
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [←rawN,hn s hs]; rfl⟩
    · have count (S : List (Finset (Fin 15) × Finset (Fin 15))) (r s : (Fin 15)) : multiplicity S r s =
          (S.filter (fun t => decide (r∈t.1 ∧ s∈t.2))).length := by
        induction S with
        | nil => rfl
        | cons t rest ih =>
          by_cases yes : r∈t.1 ∧ s∈t.2 <;> simp [multiplicity,contains,yes] at ih ⊢ <;> omega
      intro r s
      exact (count T r s).trans (unique r s)
  intro g C a b hg hC size
  let F := fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  let G := (fun x : Fin 10 → Bool => (List.finRange 5).any fun i =>
        (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
        (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
        (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2))))
  let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨g :: C.gates, 0⟩
  let W := fun (x : Fin 10 → Bool) (i : ℕ) => (D.wires (List.ofFn x)).getD i false
  let U := fun x => W x a || W x b
  change (∃ x, W x a = true ∧ W x b = false) → (∃ x, W x a = false ∧ W x b = true) →
    (∀ x, F x = false → W x a = false ∧ W x b = false) →
    ∃ x, F x = true ∧ W x a = false ∧ W x b = false
  intro ha hb off
  have same (x : Fin 10 → Bool) : G x = F x := by
    change (((x 0 && x 1) || (x 0 && x 5) || (x 5 && x 7)) || (((x 1 && x 2) || (x 1 && x 6) || (x 6 && x 8)) || (((x 2 && x 3) || (x 2 && x 7) || (x 7 && x 9)) || (((x 3 && x 4) || (x 3 && x 8) || (x 8 && x 5)) || (((x 4 && x 0) || (x 4 && x 9) || (x 9 && x 6)) || (false)))))) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
    simp only [Bool.or_false]
    ac_rfl
  have legal : PEqualNP.MetaComplexity.FanInTwo D := by
    intro gate mem
    rcases List.mem_cons.mp mem with rfl | tail
    · exact hg _ List.mem_cons_self
    · exact hC _ tail
  have budget : D.size ≤ 18 := by
    change (g :: C.gates).length ≤ 18
    change C.gates.length ≤ 17 at size
    simp only [List.length_cons]
    omega
  by_contra missed
  have allRows (x : Fin 10 → Bool) : U x = G x := by
    rw [same]
    change (W x a || W x b) = F x
    cases h : F x with
    | false =>
      obtain ⟨h1,h2⟩ := off x h
      rw [h1,h2]
      rfl
    | true =>
      cases h1 : W x a <;> cases h2 : W x b
      · exact False.elim (missed ⟨x,h,h1,h2⟩)
      all_goals rfl
  let last : PEqualNP.CircuitLowerBounds.Gate := ⟨.or,[a,b]⟩
  let E : PEqualNP.CircuitLowerBounds.Circuit := ⟨D.gates ++ [last],10+D.gates.length⟩
  have Elegal : PEqualNP.MetaComplexity.FanInTwo E := by
    intro gate mem
    change gate ∈ D.gates ++ [last] at mem
    rcases List.mem_append.mp mem with left|right
    · exact legal _ left
    · obtain rfl := List.mem_singleton.mp right
      exact ⟨Or.inr (Or.inl rfl),show (2 : ℕ) ≤ 2 from le_rfl⟩
  have Esmall : E.size ≤ 19 := by
    change (D.gates++[last]).length ≤ 19
    change D.gates.length ≤ 18 at budget
    simp only [List.length_append,List.length_cons,List.length_nil]
    omega
  let next := fun (w : List Bool) (h : PEqualNP.CircuitLowerBounds.Gate) =>
    w ++ [h.op.eval (h.inputs.map (fun i => w.getD i false))]
  have lengths (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
      (gs.foldl next w).length = w.length+gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons gate rest ih =>
      simp only [List.foldl_cons,ih,next,List.length_append,List.length_cons,List.length_nil]
      omega
  have realizes (x : Fin 10 → Bool) : E.eval (List.ofFn x) = G x := by
    rw [←allRows x]
    let w := D.wires (List.ofFn x)
    have len : w.length = 10+D.gates.length := by
      change (D.gates.foldl next (List.ofFn x)).length = 10+D.gates.length
      simpa only [List.length_ofFn] using lengths D.gates (List.ofFn x)
    change ((D.gates++[last]).foldl next (List.ofFn x)).getD (10+D.gates.length) false =
      (w.getD a false || w.getD b false)
    rw [List.foldl_append]
    change (w++[last.op.eval (last.inputs.map (fun i => w.getD i false))]).getD (10+D.gates.length) false = _
    rw [←len,List.getD_append_right w _ false w.length le_rfl,Nat.sub_self]
    change ((w.getD a false || (w.getD b false || false))) = _
    simp only [Bool.or_false]
  obtain ⟨M,hm,hs,he⟩ := helim E Elegal realizes
  let P := fun (r : Fin 15) (v : Fin 10) => (401849741469506565305680851550143442694707203 : ℕ).testBit (10*r.val+v.val)
  let N := fun (r : Fin 15) (v : Fin 10) => (1078453559198442499535953780770134430129919026 : ℕ).testBit (10*r.val+v.val)
  have pos : ∀ r, G (P r) = true := by decide +kernel
  have neg : ∀ s, G (N s) = false := by decide +kernel
  obtain ⟨T,hT,hw,hq⟩ := hpart M hm (fun r => (he _).trans (pos r)) (fun s => (he _).trans (neg s))
  have minimum := hrect T hw hq
  omega
