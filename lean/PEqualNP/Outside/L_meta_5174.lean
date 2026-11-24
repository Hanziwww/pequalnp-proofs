import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

namespace PEqualNP.Outside.L_meta_5174

def step (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]

def run (gs : List Gate) (ws : List Bool) : List Bool :=
  gs.foldl step ws

lemma getD_snoc_eq (l : List Bool) (a : Bool) : (l ++ [a]).getD l.length false = a := by
  rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]

lemma getD_snoc_ne (l : List Bool) (a : Bool) (j : ℕ) (hj : j ≠ l.length) :
    (l ++ [a]).getD j false = l.getD j false := by
  by_cases hlt : j < l.length
  · exact List.getD_append _ _ _ _ hlt
  · rw [List.getD_eq_default (l ++ [a]) false (n := j) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
        List.getD_eq_default l false (n := j) (by omega)]

lemma run_getD_lt (gs : List Gate) (ws : List Bool) (i : ℕ) (hi : i < ws.length) :
    (run gs ws).getD i false = ws.getD i false := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g rest ih =>
    simp only [run, List.foldl_cons] at ih ⊢
    have hi' : i < (step ws g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
    rw [ih (step ws g) hi']
    exact List.getD_append _ _ _ _ hi

lemma run_cons (g : Gate) (gs : List Gate) (ws : List Bool) :
    run (g :: gs) ws = run gs (step ws g) := rfl

lemma run_getD_gate (gs : List Gate) (ws : List Bool) (j : ℕ) (g : Gate)
    (hj : gs[j]? = some g) (hback : ∀ i ∈ g.inputs, i < ws.length + j) :
    (run gs ws).getD (ws.length + j) false =
      g.op.eval (g.inputs.map fun i => (run gs ws).getD i false) := by
  induction gs generalizing ws j with
  | nil => cases hj
  | cons g0 rest ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      simp only [Nat.add_zero] at hback ⊢
      rw [run_cons]
      have hlt : ws.length < (step ws g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
      rw [run_getD_lt rest (step ws g0) ws.length hlt]
      have hstep : (step ws g0).getD ws.length false =
          g0.op.eval (g0.inputs.map fun k => ws.getD k false) := getD_snoc_eq ws _
      rw [hstep]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hlti : i < ws.length := hback i hi
      have hlti' : i < (step ws g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
      rw [run_getD_lt rest (step ws g0) i hlti']
      exact (List.getD_append _ _ _ _ hlti).symm
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      rw [run_cons]
      have hlen : (step ws g0).length = ws.length + 1 := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
      have hidx : ws.length + (j' + 1) = (step ws g0).length + j' := by omega
      rw [hidx]
      exact ih (step ws g0) j' hj (fun i hi => by have := hback i hi; omega)

lemma run_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w1 w2 : List Bool) (hlen : w1.length = w2.length)
    (hle : ∀ i, w1.getD i false = true → w2.getD i false = true) :
    (run gs w1).length = (run gs w2).length ∧
      ∀ i, (run gs w1).getD i false = true → (run gs w2).getD i false = true := by
  induction gs generalizing w1 w2 with
  | nil => exact ⟨hlen, hle⟩
  | cons g rest ih =>
    simp only [run, List.foldl_cons]
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hgs g List.mem_cons_self
    have hbit : g.op.eval (g.inputs.map fun i => w1.getD i false) = true →
        g.op.eval (g.inputs.map fun i => w2.getD i false) = true := by
      rcases hg with hop | hop
      · rw [hop]
        change (g.inputs.map fun i => w1.getD i false).all id = true →
          (g.inputs.map fun i => w2.getD i false).all id = true
        intro hall
        rw [List.all_eq_true] at hall ⊢
        intro b hb
        rw [List.mem_map] at hb
        obtain ⟨i, hi, rfl⟩ := hb
        exact hle i (hall (w1.getD i false) (List.mem_map_of_mem hi))
      · rw [hop]
        change (g.inputs.map fun i => w1.getD i false).any id = true →
          (g.inputs.map fun i => w2.getD i false).any id = true
        intro hany
        rw [List.any_eq_true] at hany ⊢
        obtain ⟨b, hb, hbt⟩ := hany
        rw [List.mem_map] at hb
        obtain ⟨i, hi, rfl⟩ := hb
        exact ⟨w2.getD i false, List.mem_map_of_mem hi, hle i hbt⟩
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')) (step w1 g) (step w2 g)
    · simp only [step, List.length_append, hlen, List.length_cons, List.length_nil]
    · intro i hi
      dsimp only [step] at hi ⊢
      by_cases heq : i = w1.length
      · subst heq
        rw [getD_snoc_eq w1 _] at hi
        rw [hlen, getD_snoc_eq w2 _]
        exact hbit hi
      · have heq2 : i ≠ w2.length := by rw [← hlen]; exact heq
        rw [getD_snoc_ne w1 _ i heq] at hi
        rw [getD_snoc_ne w2 _ i heq2]
        exact hle i hi

end PEqualNP.Outside.L_meta_5174

theorem PEqualNP.Outside.L_meta_5174 :
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 x1 x2 →     ∀ (x4 x5 : Fin x1 → Bool),       (∀ (x6 : Fin x1), x4 x6 = Bool.true → x5 x6 = Bool.true) →         have x7 : (Fin x1 → Bool) → ℕ → Bool := fun (x7 : Fin x1 → Bool) (x8 : ℕ) => (x2.wires (List.ofFn x7)).getD x8 Bool.false;         (∀ (x8 : Fin x1), x7 x5 ↑x8 = x5 x8) ∧ ∀ (x8 : ℕ) (x9 : PEqualNP.CircuitLowerBounds.Gate) (x10 : ℕ), x2.gates[x8]? = Option.some x9 → x10 ∈ x9.inputs → x7 x5 (x1 + x8) = Bool.false → (x9.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∀ x14 ∈ x9.inputs, x14 ≠ x10 → x7 x4 x14 = Bool.true) → x7 x5 x10 = Bool.false := by
  intro n C hAO x y hxy
  dsimp only
  obtain ⟨handor, hreads, _⟩ := hAO
  have hmono : ∀ i : ℕ, (C.wires (List.ofFn x)).getD i false = true →
      (C.wires (List.ofFn y)).getD i false = true := by
    have hbase : ∀ i : ℕ, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
      intro i hi
      by_cases hlt : i < n
      · have hlt_x : i < (List.ofFn x).length := by simp only [List.length_ofFn]; exact hlt
        have hlt_y : i < (List.ofFn y).length := by simp only [List.length_ofFn]; exact hlt
        rw [List.getD_eq_getElem _ _ hlt_x, List.getElem_ofFn] at hi
        rw [List.getD_eq_getElem _ _ hlt_y, List.getElem_ofFn]
        exact hxy ⟨i, hlt⟩ hi
      · rw [List.getD_eq_default (List.ofFn x) false (n := i) (by simp only [List.length_ofFn]; omega)] at hi
        cases hi
    exact (PEqualNP.Outside.L_meta_5174.run_mono C.gates handor (List.ofFn x) (List.ofFn y)
      (by simp only [List.length_ofFn]) hbase).2
  constructor
  · intro i
    have hi : i.val < (List.ofFn y).length := by simp only [List.length_ofFn]; exact i.isLt
    change (PEqualNP.Outside.L_meta_5174.run C.gates (List.ofFn y)).getD i.val false = y i
    rw [PEqualNP.Outside.L_meta_5174.run_getD_lt C.gates (List.ofFn y) i.val hi,
        List.getD_eq_getElem _ _ hi, List.getElem_ofFn]
  · intro j g u hj hu hfalse hdisj
    have hj_lt : j < C.gates.length := by
      have h1 := (List.getElem?_eq_some_iff).mp hj
      exact h1.1
    have hgat : gateAt C j = g := by
      have h1 := (List.getElem?_eq_some_iff).mp hj
      change C.gates.getD j ⟨GateOp.or, []⟩ = g
      rw [List.getD_eq_getElem _ _ hj_lt]
      exact h1.2
    have hmem_g : g ∈ C.gates := by
      have h1 := (List.getElem?_eq_some_iff).mp hj
      rw [← h1.2]
      exact List.getElem_mem hj_lt
    have hback : ∀ i ∈ g.inputs, i < (List.ofFn y).length + j := by
      intro i hi
      simp only [List.length_ofFn]
      have hb := hreads j hj_lt i
      rw [hgat] at hb
      exact hb hi
    have heval : (C.wires (List.ofFn y)).getD (n + j) false =
        g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn y)).getD i false) := by
      have hw : C.wires (List.ofFn y) = PEqualNP.Outside.L_meta_5174.run C.gates (List.ofFn y) := rfl
      rw [hw]
      have h := PEqualNP.Outside.L_meta_5174.run_getD_gate C.gates (List.ofFn y) j g hj hback
      simpa only [List.length_ofFn] using h
    rw [heval] at hfalse
    cases hval : (C.wires (List.ofFn y)).getD u false
    · rfl
    · exfalso
      have hor_contra (hor : g.op = GateOp.or) : False := by
        rw [hor] at hfalse
        have htrue : GateOp.or.eval (g.inputs.map fun i => (C.wires (List.ofFn y)).getD i false) = true := by
          change (g.inputs.map fun i => (C.wires (List.ofFn y)).getD i false).any id = true
          rw [List.any_eq_true]
          exact ⟨(C.wires (List.ofFn y)).getD u false, List.mem_map_of_mem hu, hval⟩
        rw [htrue] at hfalse
        cases hfalse
      rcases hdisj with hor | hall4
      · exact hor_contra hor
      · rcases handor g hmem_g with hand | hor
        · rw [hand] at hfalse
          have htrue : GateOp.and.eval (g.inputs.map fun i => (C.wires (List.ofFn y)).getD i false) = true := by
            change (g.inputs.map fun i => (C.wires (List.ofFn y)).getD i false).all id = true
            rw [List.all_eq_true]
            intro b hb
            rw [List.mem_map] at hb
            obtain ⟨v, hv, rfl⟩ := hb
            by_cases hvu : v = u
            · subst hvu; exact hval
            · exact hmono v (hall4 v hv hvu)
          rw [htrue] at hfalse
          cases hfalse
        · exact hor_contra hor
