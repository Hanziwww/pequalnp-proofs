import Mathlib.Data.List.GetD
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

namespace PEqualNP.Outside.L_meta_3264

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma run_suffix (gs : List Gate) (w : List Bool) :
    ∃ t, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simpa using hl⟩
    simpa [step, List.append_assoc] using ht

lemma wires_length (C : Circuit) (w : List Bool) :
    (C.wires w).length = w.length + C.size := by
  obtain ⟨t, ht, hl⟩ := run_suffix C.gates w
  change (C.gates.foldl step w).length = _
  simp [ht, hl, Circuit.size]

lemma input_read {q : ℕ} (C : Circuit) (x : Fin q → Bool) (i : Fin q) :
    (C.wires (List.ofFn x)).getD i false = x i := by
  obtain ⟨t, ht, _⟩ := run_suffix C.gates (List.ofFn x)
  change (C.gates.foldl step (List.ofFn x)).getD i false = _
  rw [ht, List.getD_append _ _ _ _ (by simp),
    List.getD_eq_getElem _ _ (by simp)]
  simp

lemma read_snoc (w : List Bool) (v : Bool) (i : ℕ) :
    (w ++ [v]).getD i false = if i = w.length then v else w.getD i false := by
  by_cases he : i = w.length
  · subst i
    simp
  rw [ite_eq_right he]
  by_cases hl : i < w.length
  · exact List.getD_append _ _ _ _ hl
  rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

-- Insert k unused inputs just before wire cut. All later wires shift together.
def move (cut k i : ℕ) : ℕ := if i < cut then i else k + i

def movedGate (cut k : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (move cut k)⟩

def moved (cut k : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (movedGate cut k), move cut k C.output⟩

lemma moved_size (cut k : ℕ) (C : Circuit) : (moved cut k C).size = C.size := by
  simp [moved, Circuit.size]

lemma moved_ao {q cut k : ℕ} {C : Circuit} (h : IsAO2 q C) :
    IsAO2 (k + q) (moved cut k C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
    exact h.1 u hu
  · intro j hj i hi
    have hj' : j < C.gates.length := by simpa [moved] using hj
    have gate_eq : gateAt (moved cut k C) j = movedGate cut k (gateAt C j) := by
      unfold gateAt
      rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj']
      simp [moved]
    rw [gate_eq] at hi
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hi
    have hb := h.2.1 j hj' t ht
    unfold move
    split <;> omega
  · intro g hg
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
    simpa [movedGate] using h.2.2 u hu

lemma moved_run (cut k : ℕ) (gs : List Gate) (w v : List Bool)
    (hc : cut ≤ w.length) (hl : v.length = k + w.length)
    (hm : ∀ i, v.getD (move cut k i) false = w.getD i false) (i : ℕ) :
    ((gs.map (movedGate cut k)).foldl step v).getD (move cut k i) false =
      (gs.foldl step w).getD i false := by
  induction gs generalizing w v with
  | nil => exact hm i
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · simp [step]; omega
    · simp [step, hl, Nat.add_assoc]
    · intro j
      have hnew : move cut k j = v.length ↔ j = w.length := by
        unfold move
        split <;> omega
      simp only [step, movedGate, List.map_map, Function.comp_def, hm, read_snoc, hnew]

def embed {q : ℕ} (cut k : ℕ) (i : Fin q) : Fin (k + q) :=
  ⟨move cut k i, by unfold move; split <;> have := i.isLt <;> omega⟩

lemma moved_eval {q cut k : ℕ} (hc : cut ≤ q) (C : Circuit) (x : Fin (k+q) → Bool) :
    circuitFun (k+q) (moved cut k C) x = circuitFun q C (fun i => x (embed cut k i)) := by
  apply moved_run cut k C.gates (List.ofFn fun i => x (embed cut k i)) (List.ofFn x)
  · simpa using hc
  · simp
  · intro i
    by_cases hi : i < q
    · have hi' := (embed cut k (⟨i, hi⟩ : Fin q)).isLt
      change move cut k i < k + q at hi'
      rw [List.getD_eq_getElem _ _ (by simpa using hi'),
        List.getD_eq_getElem _ _ (by simpa using hi)]
      simp [embed]
    · have hm : k + q ≤ move cut k i := by
        simp [move, show ¬ i < cut by omega]; omega
      rw [List.getD_eq_default _ _ (by simpa using hm),
        List.getD_eq_default _ _ (by simp; omega)]

def appendGate (q : ℕ) (C : Circuit) (op : GateOp) (u v : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨op, [u, v]⟩], q + C.size⟩

lemma append_size (q : ℕ) (C : Circuit) (op : GateOp) (u v : ℕ) :
    (appendGate q C op u v).size = C.size + 1 := by simp [appendGate, Circuit.size]

lemma append_ao {q : ℕ} {C : Circuit} {op : GateOp} {u v : ℕ} (h : IsAO2 q C)
    (hop : op = .and ∨ op = .or) (hu : u < q + C.size) (hv : v < q + C.size) :
    IsAO2 q (appendGate q C op u v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with old | last
    · exact h.1 g old
    · obtain rfl := List.mem_singleton.mp last
      exact hop
  · intro j hj i hi
    by_cases old : j < C.gates.length
    · have hg : gateAt (appendGate q C op u v) j = gateAt C j :=
        List.getD_append _ _ _ _ old
      rw [hg] at hi
      exact h.2.1 j old i hi
    · have last : j = C.gates.length := by
        simp [appendGate] at hj
        omega
      subst j
      simp [gateAt, appendGate] at hi
      rcases hi with rfl | rfl
      · exact hu
      · exact hv
  · intro g hg
    rcases List.mem_append.mp hg with old | last
    · exact h.2.2 g old
    · obtain rfl := List.mem_singleton.mp last
      rfl

lemma append_wires (q : ℕ) (C : Circuit) (op : GateOp) (u v : ℕ) (x : List Bool) :
    (appendGate q C op u v).wires x =
      C.wires x ++ [op.eval [(C.wires x).getD u false, (C.wires x).getD v false]] := by
  simp [appendGate, Circuit.wires, List.foldl_append]

lemma append_value {q : ℕ} (C : Circuit) (op : GateOp) (u v : ℕ) (x : Fin q → Bool) :
    circuitFun q (appendGate q C op u v) x =
      op.eval [(C.wires (List.ofFn x)).getD u false, (C.wires (List.ofFn x)).getD v false] := by
  have len : (C.wires (List.ofFn x)).length = q + C.size := by simp [wires_length]
  unfold circuitFun Circuit.eval
  rw [append_wires, read_snoc]
  simp [appendGate, len]

def addPair {q : ℕ} (C : Circuit) (u v : Fin q) : Circuit :=
  appendGate q (appendGate q C .and u v) .or C.output (q + C.size)

lemma pair_spec {q : ℕ} {C : Circuit} (u v : Fin q) (h : IsAO2 q C)
    (hout : C.output < q + C.size) :
    IsAO2 q (addPair C u v) ∧ (addPair C u v).size = C.size + 2 ∧
      (addPair C u v).output < q + (addPair C u v).size ∧
      ∀ x, circuitFun q (addPair C u v) x =
        (circuitFun q C x || (x u && x v)) := by
  have hAnd : IsAO2 q (appendGate q C .and u v) :=
    append_ao h (Or.inl rfl) (by have := u.isLt; omega) (by have := v.isLt; omega)
  refine ⟨append_ao hAnd (Or.inr rfl) (by rw [append_size]; omega)
    (by rw [append_size]; omega), ?_, ?_, ?_⟩
  · simp [addPair, append_size, Nat.add_assoc]
  · change q + (appendGate q C .and u v).size < q + (addPair C u v).size
    simp [addPair, append_size, Nat.add_assoc]
  · intro x
    have len : (C.wires (List.ofFn x)).length = q + C.size := by simp [wires_length]
    have ne : C.output ≠ q + C.size := by omega
    rw [addPair, append_value, append_wires]
    simp only [read_snoc, len, ite_eq_right ne, input_read]
    simp [GateOp.eval, circuitFun, Circuit.eval]

def hit {n m : ℕ} (E : Finset (Fin n × Fin m)) (x : Fin (n + m) → Bool) : Prop :=
  ∃ a b, (a, b) ∈ E ∧ x (Fin.castAdd m a) = true ∧ x (Fin.natAdd n b) = true

def liftEdges {n m : ℕ} (E : Finset (Fin n × Fin m)) : Finset (Fin (n+m) × Fin (n+m)) :=
  E.image fun p => (Fin.castAdd m p.1, Fin.natAdd n p.2)

lemma embed_left {n m : ℕ} (a : Fin n) :
    embed n (n+m) (Fin.castAdd m a) = Fin.castAdd (n+m) (Fin.castAdd m a) := by
  apply Fin.ext
  simp [embed, move, a.isLt]

lemma embed_right {n m : ℕ} (b : Fin m) :
    embed n (n+m) (Fin.natAdd n b) = Fin.natAdd (n+m) (Fin.natAdd n b) := by
  apply Fin.ext
  simp [embed, move]
  omega

lemma hit_lift {n m : ℕ} (E : Finset (Fin n × Fin m)) (x : Fin ((n+m)+(n+m)) → Bool) :
    hit E (fun i => x (embed n (n+m) i)) ↔ hit (liftEdges E) x := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    exact ⟨Fin.castAdd m a, Fin.natAdd n b, Finset.mem_image.mpr ⟨(a,b), hab, rfl⟩,
      by simpa only [embed_left] using ha, by simpa only [embed_right] using hb⟩
  · rintro ⟨a, b, hab, ha, hb⟩
    obtain ⟨⟨p,l⟩, hpl, eq⟩ := Finset.mem_image.mp hab
    change (Fin.castAdd m p, Fin.natAdd n l) = (a,b) at eq
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    exact ⟨p, l, hpl, by simpa only [embed_left] using ha,
      by simpa only [embed_right] using hb⟩

lemma hit_insert {n : ℕ} (S : Finset (Fin n × Fin n)) (e : Fin n × Fin n)
    (x : Fin (n+n) → Bool) :
    hit (insert e S) x ↔ hit S x ∨ (x (Fin.castAdd n e.1) = true ∧ x (Fin.natAdd n e.2) = true) := by
  constructor
  · rintro ⟨a,b,hm,ha,hb⟩
    rcases Finset.mem_insert.mp hm with he | hs
    · subst e
      exact Or.inr ⟨ha,hb⟩
    · exact Or.inl ⟨a,b,hs,ha,hb⟩
  · rintro (⟨a,b,hs,ha,hb⟩ | ⟨ha,hb⟩)
    · exact ⟨a,b,Finset.mem_insert_of_mem hs,ha,hb⟩
    · exact ⟨e.1,e.2,Finset.mem_insert_self _ _,ha,hb⟩

lemma extend_edges {n : ℕ} (A : Finset (Fin n × Fin n)) (C : Circuit)
    (hAO : IsAO2 (n+n) C) (hout : C.output < n+n+C.size)
    (hfun : ∀ x, circuitFun (n+n) C x = true ↔ hit A x) (B : Finset (Fin n × Fin n)) :
    ∃ D : Circuit, IsAO2 (n+n) D ∧ D.size ≤ C.size + 2*B.card ∧
      D.output < n+n+D.size ∧ ∀ x, circuitFun (n+n) D x = true ↔ hit (A ∪ B) x := by
  induction B using Finset.induction_on with
  | empty => exact ⟨C, hAO, by simp, hout, by simpa using hfun⟩
  | @insert e B fresh ih =>
    obtain ⟨D,hD,hs,ho,hf⟩ := ih
    obtain ⟨hD',hs',ho',hf'⟩ := pair_spec (Fin.castAdd n e.1) (Fin.natAdd n e.2) hD ho
    refine ⟨_, hD', ?_, ho', ?_⟩
    · rw [hs', Finset.card_insert_of_notMem fresh]
      omega
    · intro x
      have union_eq : A ∪ insert e B = insert e (A ∪ B) := by
        ext t
        simp only [Finset.mem_union, Finset.mem_insert]
        tauto
      rw [hf', Bool.or_eq_true, Bool.and_eq_true, hf, union_eq, hit_insert]

lemma output_lt_of_true {q : ℕ} {C : Circuit} {x : Fin q → Bool}
    (h : circuitFun q C x = true) : C.output < q + C.size := by
  by_contra! ho
  change (C.wires (List.ofFn x)).getD C.output false = true at h
  rw [List.getD_eq_default _ _ (by simpa [wires_length] using ho)] at h
  contradiction

end PEqualNP.Outside.L_meta_3264

open PEqualNP.Outside.L_meta_3264

theorem PEqualNP.Outside.L_meta_3264 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x3.Nonempty →     PEqualNP.TopForm.IsAO2 (x1 + x2) x4 →       (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) →         let x8 : ℕ := x1 + x2;         have x9 : Finset (Fin (x1 + x2) × Fin (x1 + x2)) := Finset.image (fun (x9 : Fin x1 × Fin x2) => (Fin.castAdd x2 x9.1, Fin.natAdd x1 x9.2)) x3;         ∀ (x10 : Finset (Fin x8 × Fin x8)), ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x8 + x8) x11 ∧ x11.size ≤ x4.size + (2 : ℕ) * x10.card ∧ ∀ (x12 : Fin (x8 + x8) → Bool), PEqualNP.MetaComplexity.circuitFun (x8 + x8) x11 x12 = Decidable.decide (∃ (x13 : Fin (x1 + x2)) (x14 : Fin (x1 + x2)), (x13, x14) ∈ x9 ∪ x10 ∧ x12 (Fin.castAdd x8 x13) = Bool.true ∧ x12 (Fin.natAdd x8 x14) = Bool.true) := by
  intro n m E C nonempty hAO hfun
  dsimp only
  intro B
  obtain ⟨⟨a,b⟩, he⟩ := nonempty
  have on : circuitFun (n+m) C (fun _ => true) = true := by
    rw [hfun, decide_eq_true_iff]
    exact ⟨a,b,he,rfl,rfl⟩
  have ho := output_lt_of_true on
  let C' := moved n (n+m) C
  have ho' : C'.output < (n+m)+(n+m)+C'.size := by
    change move n (n+m) C.output < (n+m)+(n+m)+(moved n (n+m) C).size
    rw [moved_size]
    unfold move
    split <;> omega
  have hf (x : Fin ((n+m)+(n+m)) → Bool) :
      circuitFun ((n+m)+(n+m)) C' x = true ↔ hit (liftEdges E) x := by
    rw [moved_eval (by omega), hfun, decide_eq_true_iff]
    exact hit_lift E x
  obtain ⟨D, hD, hs, _, hv⟩ := extend_edges (liftEdges E) C' (moved_ao hAO) ho' hf B
  refine ⟨D, hD, ?_, ?_⟩
  · simpa only [C', moved_size] using hs
  · intro x
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact hv x
