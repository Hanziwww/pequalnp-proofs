import Mathlib
import PEqualNP.Defs

-- The wire and OR-closure lemmas below follow L_meta_1598; the rest is the descent argument.
namespace PEqualNP.Outside.L_meta_3756

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadK

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

lemma orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

lemma orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact orStep_getD_lt n cs g k hk

lemma orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, orFold_getD_lt n post _ m (by omega)]
    exact orStep_getD_lt n _ gk m (by omega)
  have h3 := orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩

lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

lemma coneStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (coneStep n cs g).getD cs.length [] ↔ ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧
      (x = w - n ∨ x ∈ cs.getD (w - n) []) := by
  simp only [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl,
    Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, List.mem_flatMap, List.mem_filter,
    decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, hx⟩
    exact ⟨w, hw, hn, hlt, hx⟩
  · rintro ⟨w, hw, hn, hlt, hx⟩
    exact ⟨w, ⟨hw, hn, hlt⟩, hx⟩

lemma cones_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (cones n C).getD k [] ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (x = w - n ∨ x ∈ (cones n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] = (coneStep n (pre.foldl (coneStep n) []) gk).getD k [] := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  have h3 := coneStep_mem_last n (pre.foldl (coneStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro ⟨w, hw, hn, hlt, hx⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (by rw [h2 (w - n) (by omega)]; exact hx)
  · rintro ⟨w, hw, hn, hlt, hx⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (by rw [← h2 (w - n) (by omega)]; exact hx)

def rvG (S : List ℕ) (k : ℕ) (look : ℕ → List (List ℕ)) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.or => (g.inputs.map look).foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => (g.inputs.map look).foldl (andStep k) [S.map fun _ => 0]
  | _ => []

def rvStep (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) :
    List (List (List ℕ)) :=
  R ++ [rvG S k (fun i => R.getD i []) g]

lemma readVectors_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = C.gates.foldl (rvStep S k) ((List.range n).map (leafVectors S k)) :=
  rfl

lemma rvFold_length (S : List ℕ) (k : ℕ) (gs : List Gate) (R : List (List (List ℕ))) :
    (gs.foldl (rvStep S k) R).length = R.length + gs.length := by
  induction gs generalizing R with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [rvStep]
    omega

lemma rvStep_getD_lt (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) (m : ℕ)
    (hm : m < R.length) : (rvStep S k R g).getD m [] = R.getD m [] := by
  simp [rvStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma rvFold_getD_lt (S : List ℕ) (k : ℕ) (gs : List Gate) (R : List (List (List ℕ))) (m : ℕ)
    (hm : m < R.length) : (gs.foldl (rvStep S k) R).getD m [] = R.getD m [] := by
  induction gs generalizing R with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (rvStep S k R g) (by simp [rvStep]; omega)]
    exact rvStep_getD_lt S k R g m hm

lemma rv_gate (C : Circuit) (n : ℕ) (S : List ℕ) (kk j : ℕ) (hj : j < C.gates.length) :
    (readVectors C n S kk).getD (n + j) [] =
      rvG S kk (fun i => if i < n + j then (readVectors C n S kk).getD i [] else [])
        (gateAt C j) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates j hj
  have hga : gateAt C j = gj := by rw [gateAt_eq C j hj]; exact hgj
  rw [hga]
  let R0 := pre.foldl (rvStep S kk) ((List.range n).map (leafVectors S kk))
  have hR0 : R0.length = n + j := by simp [R0, rvFold_length, hpre_len]
  have hfull : readVectors C n S kk = post.foldl (rvStep S kk) (rvStep S kk R0 gj) := by
    rw [readVectors_eq, hgs, List.foldl_append, List.foldl_cons]
  have hlen1 : (rvStep S kk R0 gj).length = n + j + 1 := by simp [rvStep, hR0]
  rw [hfull, rvFold_getD_lt S kk post _ (n + j) (by omega)]
  have hlast : (rvStep S kk R0 gj).getD (n + j) [] = rvG S kk (fun i => R0.getD i []) gj := by
    simp only [rvStep, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega), hR0, Nat.sub_self]
    simp
  rw [hlast]
  congr 1
  funext i
  by_cases hi : i < n + j
  · rw [if_pos hi, rvFold_getD_lt S kk post _ i (by omega), rvStep_getD_lt S kk R0 gj i (by omega)]
  · rw [if_neg hi]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : R0.length ≤ i)]

lemma rv_input (C : Circuit) (n : ℕ) (S : List ℕ) (kk i : ℕ) (hi : i < n) :
    (readVectors C n S kk).getD i [] = leafVectors S kk i := by
  rw [readVectors_eq, rvFold_getD_lt S kk C.gates _ i (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

lemma insertNew_mem_self (A : List (List ℕ)) (v : List ℕ) : v ∈ insertNew A v := by
  unfold insertNew
  split_ifs with h
  · exact h
  · simp

lemma insertNew_mem_of_mem (A : List (List ℕ)) (v x : List ℕ) (hx : x ∈ A) :
    x ∈ insertNew A v := by
  unfold insertNew
  split_ifs
  · exact hx
  · exact List.mem_append_left _ hx

lemma foldl_insertNew_acc (L acc : List (List ℕ)) (x : List ℕ) (hx : x ∈ acc) :
    x ∈ L.foldl insertNew acc := by
  induction L generalizing acc with
  | nil => exact hx
  | cons a L ih => exact ih _ (insertNew_mem_of_mem acc a x hx)

lemma foldl_insertNew_mem (L acc : List (List ℕ)) (x : List ℕ) (hx : x ∈ L) :
    x ∈ L.foldl insertNew acc := by
  induction L generalizing acc with
  | nil => simp at hx
  | cons a L ih =>
    rcases List.mem_cons.mp hx with rfl | h
    · exact foldl_insertNew_acc L _ _ (insertNew_mem_self acc _)
    · exact ih _ h

lemma orFoldV_acc (Ls : List (List (List ℕ))) (acc : List (List ℕ)) (x : List ℕ) (hx : x ∈ acc) :
    x ∈ Ls.foldl (fun acc A => A.foldl insertNew acc) acc := by
  induction Ls generalizing acc with
  | nil => exact hx
  | cons A Ls ih => exact ih _ (foldl_insertNew_acc A acc x hx)

lemma orFoldV_mem (Ls : List (List (List ℕ))) (acc : List (List ℕ)) (A : List (List ℕ))
    (hA : A ∈ Ls) (x : List ℕ) (hx : x ∈ A) :
    x ∈ Ls.foldl (fun acc A => A.foldl insertNew acc) acc := by
  induction Ls generalizing acc with
  | nil => simp at hA
  | cons B Ls ih =>
    rcases List.mem_cons.mp hA with rfl | h
    · exact orFoldV_acc Ls _ x (foldl_insertNew_mem A acc x hx)
    · exact ih _ h

lemma andStep_mem (kk : ℕ) (A B : List (List ℕ)) (a b : List ℕ) (ha : a ∈ A) (hb : b ∈ B) :
    capAdd kk a b ∈ andStep kk A B := by
  unfold andStep
  apply foldl_insertNew_mem
  exact List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨b, hb, rfl⟩⟩

lemma rvG_or_mem (S : List ℕ) (kk : ℕ) (look : ℕ → List (List ℕ)) (g : Gate)
    (hop : g.op = GateOp.or) (i : ℕ) (hi : i ∈ g.inputs) (x : List ℕ) (hx : x ∈ look i) :
    x ∈ rvG S kk look g := by
  unfold rvG
  rw [hop]
  exact orFoldV_mem _ [] (look i) (List.mem_map.mpr ⟨i, hi, rfl⟩) x hx

lemma rvG_and_mem (S : List ℕ) (kk : ℕ) (look : ℕ → List (List ℕ)) (g : Gate)
    (hop : g.op = GateOp.and) (a b : ℕ) (hin : g.inputs = [a, b]) (va vb : List ℕ)
    (ha : va ∈ look a) (hb : vb ∈ look b) :
    capAdd kk (capAdd kk (S.map fun _ => 0) va) vb ∈ rvG S kk look g := by
  unfold rvG
  rw [hop, hin]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  exact andStep_mem kk _ _ _ _ (andStep_mem kk _ _ _ _ (List.mem_singleton_self _) ha) hb

def Pat1 (n : ℕ) (C : Circuit) (u v : Fin n) : Prop :=
  ∃ X < C.gates.length, ∃ Y < C.gates.length, ∃ (A Q P N : ℕ) (z w : Fin n),
    InOutputCone n C X ∧ (gateAt C X).op = GateOp.and ∧
    ((gateAt C X).inputs = [A, Q] ∨ (gateAt C X).inputs = [Q, A]) ∧
    (gateAt C Y).op = GateOp.and ∧
    ((gateAt C Y).inputs = [P, N] ∨ (gateAt C Y).inputs = [N, P]) ∧
    OrReaches n C Q Y ∧ ((z = u ∧ w = v) ∨ (z = v ∧ w = u)) ∧
    z ∈ orIn n C A ∧ z ∈ orIn n C P ∧ w ∈ orIn n C N

def Pat2 (n : ℕ) (C : Circuit) (u v : Fin n) : Prop :=
  ∃ Wg < C.gates.length, ∃ L M : ℕ, InOutputCone n C Wg ∧ (gateAt C Wg).op = GateOp.and ∧
    (gateAt C Wg).inputs = [L, M] ∧ gateVal n C Wg (pairInput u v) = true ∧
    u ∉ orIn n C L ∧ v ∉ orIn n C L ∧ u ∉ orIn n C M ∧ v ∉ orIn n C M

lemma orSets_length (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  simp [orSets, orFold_length]

lemma orSets_le (n : ℕ) (C : Circuit) :
    ∀ k, k < C.gates.length → ∀ x, x ∈ (orSets n C).getD k [] → x ≤ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk x hx
    rcases (orSets_mem_iff n C k x hk).1 hx with rfl | ⟨_, w, _, hn, hlt, hxw⟩
    · exact le_refl _
    · have := ih (w - n) (by omega) (by omega) x hxw
      omega

lemma orReach_bound (n : ℕ) (C : Circuit) (w g : ℕ) (h : OrReaches n C w g) :
    n ≤ w ∧ w - n < C.gates.length ∧ g ≤ w - n := by
  obtain ⟨hn, hg⟩ := h
  have hlt : w - n < C.gates.length := by
    by_contra hc
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [orSets_length]; omega)] at hg
    simp at hg
  exact ⟨hn, hlt, orSets_le n C (w - n) hlt g hg⟩

lemma orReach_self (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) k :=
  ⟨by omega, by rw [show n + k - n = k by omega]; exact (orSets_mem_iff n C k k hk).2 (Or.inl rfl)⟩

lemma orReach_val (n : ℕ) (C : Circuit) (y : Fin n → Bool) :
    ∀ w g, OrReaches n C w g → W n C y (n + g) = true → W n C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro g hg hv
    obtain ⟨hn, hlt, _⟩ := orReach_bound n C w g hg
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    have hmem := hg.2
    rw [show n + k - n = k by omega] at hmem
    rcases (orSets_mem_iff n C k g hk).1 hmem with rfl | ⟨hop, w', hw', hn', hlt', hg'⟩
    · exact hv
    · have hw'v : W n C y w' = true := ih w' (by omega) g ⟨hn', hg'⟩ hv
      rw [W_gate n C y k hk, hop]
      simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
      exact ⟨w', hw', by simp only [hlt', ite_true]; exact hw'v⟩

lemma orIn_val (n : ℕ) (C : Circuit) (y : Fin n → Bool) (w : ℕ) (i : Fin n)
    (hi : i ∈ orIn n C w) (hy : y i = true) : W n C y w = true := by
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rcases hi with h | ⟨k, hk, hr, hop, hin⟩
  · rw [← h, W_input n C y i i.isLt]
    exact hy
  · apply orReach_val n C y w k hr
    rw [W_gate n C y k hk, hop]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
    refine ⟨i, hin, ?_⟩
    have hlt : (i : ℕ) < n + k := by have := i.isLt; omega
    simp only [hlt, ite_true]
    rw [W_input n C y i i.isLt]
    exact hy

lemma descent (n : ℕ) (C : Circuit) (hAO : AndOrOnly C) (y : Fin n → Bool) :
    ∀ w, W n C y w = true →
      (∃ k, OrReaches n C w k ∧ (gateAt C k).op = GateOp.and ∧ W n C y (n + k) = true) ∨
      ∃ i : Fin n, i ∈ orIn n C w ∧ y i = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwn : w < n
    · right
      refine ⟨⟨w, hwn⟩, ?_, ?_⟩
      · simp [orIn]
      · rw [W_input n C y w hwn] at hw
        exact hw
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      by_cases hk : k < C.gates.length
      · have hmem : gateAt C k ∈ C.gates := by
          rw [gateAt_eq C k hk]
          exact List.getElem_mem hk
        have hself := orReach_self n C k hk
        rcases hAO _ hmem with hop | hop
        · exact Or.inl ⟨k, hself, hop, hw⟩
        · rw [W_gate n C y k hk, hop] at hw
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at hw
          obtain ⟨i, hi, hv⟩ := hw
          have hlt : i < n + k := by
            by_contra hc
            simp [hc] at hv
          simp only [hlt, ite_true] at hv
          rcases ih i hlt hv with ⟨g, hg, hgop, hgv⟩ | ⟨j, hj, hjv⟩
          · left
            refine ⟨g, ⟨by omega, ?_⟩, hgop, hgv⟩
            rw [show n + k - n = k by omega]
            exact (orSets_mem_iff n C k g hk).2 (Or.inr ⟨hop, i, hi, hg.1, hlt, hg.2⟩)
          · right
            refine ⟨j, ?_, hjv⟩
            simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
            right
            by_cases hin : i < n
            · rcases hj with hj | ⟨k', _, hr, _, _⟩
              · exact ⟨k, hk, hself, hop, by rw [hj]; exact hi⟩
              · exact absurd hr.1 (by omega)
            · rcases hj with hj | ⟨k', hk', hr, hop', hin'⟩
              · exact absurd hj (by have := j.isLt; omega)
              · refine ⟨k', hk', ⟨by omega, ?_⟩, hop', hin'⟩
                rw [show n + k - n = k by omega]
                exact (orSets_mem_iff n C k k' hk).2 (Or.inr ⟨hop, i, hi, hr.1, hlt, hr.2⟩)
      · exfalso
        have : W n C y (n + k) = false := by
          simp only [W]
          exact getD_ge_length _ _ (by rw [wires_length]; omega)
        rw [this] at hw
        exact Bool.false_ne_true hw

lemma inCone_lt (n : ℕ) (C : Circuit) (a c : ℕ) (h : InCone n C a c) : c < C.gates.length := by
  by_contra hc
  have hlen : (cones n C).length = C.gates.length := by simp [cones, coneFold_length]
  simp only [InCone] at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at h
  simp at h

lemma orReach_cone (n : ℕ) (C : Circuit) :
    ∀ j, j < C.gates.length → ∀ g, OrReaches n C (n + j) g → g = j ∨ InCone n C g j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj g hg
    have hmem := hg.2
    rw [show n + j - n = j by omega] at hmem
    rcases (orSets_mem_iff n C j g hj).1 hmem with rfl | ⟨_, w, hw, hn, hlt, hg'⟩
    · exact Or.inl rfl
    · right
      have hrec := ih (w - n) (by omega) (by omega) g
        ⟨by omega, by rw [show n + (w - n) - n = w - n by omega]; exact hg'⟩
      show g ∈ (cones n C).getD j []
      rw [cones_mem_iff n C j g hj]
      exact ⟨w, hw, hn, hlt, hrec⟩

lemma inCone_trans (n : ℕ) (C : Circuit) :
    ∀ c, c < C.gates.length → ∀ a b, InCone n C a b → InCone n C b c → InCone n C a c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro hc a b hab hbc
    have hbc' : b ∈ (cones n C).getD c [] := hbc
    rw [cones_mem_iff n C c b hc] at hbc'
    show a ∈ (cones n C).getD c []
    rw [cones_mem_iff n C c a hc]
    obtain ⟨w, hw, hn, hlt, hb⟩ := hbc'
    refine ⟨w, hw, hn, hlt, Or.inr ?_⟩
    rcases hb with rfl | hb
    · exact hab
    · exact ih (w - n) (by omega) (by omega) a b hab hb

lemma operand_cone (n : ℕ) (C : Circuit) (X w : ℕ) (hX : X < C.gates.length)
    (hw : w ∈ (gateAt C X).inputs) (hn : n ≤ w) (hlt : w < n + X) : InCone n C (w - n) X := by
  show w - n ∈ (cones n C).getD X []
  rw [cones_mem_iff n C X (w - n) hX]
  exact ⟨w, hw, hn, hlt, Or.inl rfl⟩

lemma cone_down (n : ℕ) (C : Circuit) (X Y : ℕ) (hX : InOutputCone n C X) (hY : Y < C.gates.length)
    (hYX : InCone n C Y X) : InOutputCone n C Y := by
  obtain ⟨_, h | ⟨hn, hc⟩⟩ := hX
  · refine ⟨hY, Or.inr ⟨by omega, ?_⟩⟩
    rw [show C.output - n = X by omega]
    exact hYX
  · exact ⟨hY, Or.inr ⟨hn, inCone_trans n C (C.output - n) (inCone_lt n C X _ hc) Y X hYX hc⟩⟩

lemma W_and (n : ℕ) (C : Circuit) (y : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) : W n C y (n + k) = (W n C y a && W n C y b) := by
  rw [W_gate n C y k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

lemma two_inputs (n : ℕ) (C : Circuit) (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (k : ℕ)
    (hk : k < C.gates.length) : ∃ a b, (gateAt C k).inputs = [a, b] := by
  have hmem : gateAt C k ∈ C.gates := by rw [gateAt_eq C k hk]; exact List.getElem_mem hk
  exact List.length_eq_two.mp (h2 _ hmem)

lemma and_disjoint (n : ℕ) (C : Circuit)
    (hone : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ∀ t : Fin n, gateVal n C k (fun r => decide (r = t)) = false)
    (k : ℕ) (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.and) (a b : ℕ)
    (hin : (gateAt C k).inputs = [a, b]) (ha : a < n + k) (hb : b < n + k) (t : Fin n)
    (hta : t ∈ orIn n C a) (htb : t ∈ orIn n C b) : False := by
  have h1 := orIn_val n C (fun r => decide (r = t)) a t hta (by simp)
  have h2 := orIn_val n C (fun r => decide (r = t)) b t htb (by simp)
  have h3 := hone k hk hop t
  have h4 := W_and n C (fun r => decide (r = t)) k hk hop a b hin ha hb
  have h5 : gateVal n C k (fun r => decide (r = t)) = W n C (fun r => decide (r = t)) (n + k) := rfl
  rw [h5, h4, h1, h2] at h3
  simp at h3

lemma rv_orReach (n : ℕ) (C : Circuit) (S : List ℕ) (kk : ℕ) (vec : List ℕ) :
    ∀ w g, OrReaches n C w g → vec ∈ (readVectors C n S kk).getD (n + g) [] →
      vec ∈ (readVectors C n S kk).getD w [] := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro g hg hv
    obtain ⟨hn, hlt, _⟩ := orReach_bound n C w g hg
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    have hmem := hg.2
    rw [show n + k - n = k by omega] at hmem
    rcases (orSets_mem_iff n C k g hk).1 hmem with rfl | ⟨hop, w', hw', hn', hlt', hg'⟩
    · exact hv
    · have hw'v := ih w' (by omega) g ⟨hn', hg'⟩ hv
      rw [rv_gate C n S kk k hk]
      apply rvG_or_mem S kk _ _ hop w' hw'
      simp only [hlt', ite_true]
      exact hw'v

lemma rv_orIn (n : ℕ) (C : Circuit) (hRB : ReadsBack n C) (S : List ℕ) (kk : ℕ) (vec : List ℕ)
    (w : ℕ) (e : Fin n) (hleaf : vec ∈ leafVectors S kk e) (he : e ∈ orIn n C w) :
    vec ∈ (readVectors C n S kk).getD w [] := by
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at he
  rcases he with h | ⟨k, hk, hr, hop, hin⟩
  · rw [← h, rv_input C n S kk e e.isLt]
    exact hleaf
  · apply rv_orReach n C S kk vec w k hr
    rw [rv_gate C n S kk k hk]
    apply rvG_or_mem S kk _ _ hop e hin
    have hlt : (e : ℕ) < n + k := by have := e.isLt; omega
    simp only [hlt, ite_true]
    rw [rv_input C n S kk e e.isLt]
    exact hleaf

lemma rv_and (n : ℕ) (C : Circuit) (S : List ℕ) (kk : ℕ) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) (va vb : List ℕ)
    (hva : va ∈ (readVectors C n S kk).getD a []) (hvb : vb ∈ (readVectors C n S kk).getD b []) :
    capAdd kk (capAdd kk (S.map fun _ => 0) va) vb ∈ (readVectors C n S kk).getD (n + k) [] := by
  rw [rv_gate C n S kk k hk]
  apply rvG_and_mem S kk _ _ hop a b hin
  · simp only [ha, ite_true]; exact hva
  · simp only [hb, ite_true]; exact hvb

lemma leaf_u (u v : ℕ) (huv : u ≠ v) : [1, 0] ∈ leafVectors [u, v] 1 u := by
  simp [leafVectors, Ne.symm huv]

lemma leaf_v (u v : ℕ) (huv : u ≠ v) : [0, 1] ∈ leafVectors [u, v] 1 v := by
  simp [leafVectors, huv]

lemma half_descend (n : ℕ) (C : Circuit) (hAO2 : IsAO2 n C)
    (hone : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ∀ t : Fin n, gateVal n C k (fun r => decide (r = t)) = false)
    (u v : Fin n) :
    ∀ X, X < C.gates.length → InOutputCone n C X → (gateAt C X).op = GateOp.and →
      W n C (pairInput u v) (n + X) = true →
      ∀ A Q (z : Fin n), ((gateAt C X).inputs = [A, Q] ∨ (gateAt C X).inputs = [Q, A]) →
        (z = u ∨ z = v) → z ∈ orIn n C A → u ∉ orIn n C Q → v ∉ orIn n C Q →
        Pat1 n C u v ∨ Pat2 n C u v := by
  obtain ⟨hAO, hRB, h2⟩ := hAO2
  intro X
  induction X using Nat.strong_induction_on with
  | _ X ih =>
    intro hX hcone hop hval A Q z hin hz hzA huQ hvQ
    have hAmem : A ∈ (gateAt C X).inputs := by rcases hin with h | h <;> rw [h] <;> simp
    have hQmem : Q ∈ (gateAt C X).inputs := by rcases hin with h | h <;> rw [h] <;> simp
    have hA_lt : A < n + X := hRB X hX A hAmem
    have hQ_lt : Q < n + X := hRB X hX Q hQmem
    have hQv : W n C (pairInput u v) Q = true := by
      rcases hin with h | h
      · rw [W_and n C _ X hX hop A Q h hA_lt hQ_lt] at hval
        simp only [Bool.and_eq_true] at hval
        exact hval.2
      · rw [W_and n C _ X hX hop Q A h hQ_lt hA_lt] at hval
        simp only [Bool.and_eq_true] at hval
        exact hval.1
    rcases descent n C hAO _ Q hQv with ⟨Y, hYr, hYop, hYv⟩ | ⟨i, hiQ, hiv⟩
    · obtain ⟨hQn, hQlt, hYle⟩ := orReach_bound n C Q Y hYr
      have hYX : Y < X := by omega
      have hY : Y < C.gates.length := by omega
      have hYinX : InCone n C Y X := by
        have hQc := operand_cone n C X Q hX hQmem hQn hQ_lt
        rcases orReach_cone n C (Q - n) hQlt Y
            (by rw [show n + (Q - n) = Q by omega]; exact hYr) with h | h
        · rw [h]; exact hQc
        · exact inCone_trans n C X hX Y (Q - n) h hQc
      have hYcone := cone_down n C X Y hcone hY hYinX
      obtain ⟨p, q, hpq⟩ := two_inputs n C h2 Y hY
      have hp_lt : p < n + Y := hRB Y hY p (by rw [hpq]; simp)
      have hq_lt : q < n + Y := hRB Y hY q (by rw [hpq]; simp)
      have hdisj := and_disjoint n C hone Y hY hYop p q hpq hp_lt hq_lt
      by_cases hRp : u ∈ orIn n C p ∨ v ∈ orIn n C p
      · by_cases hRq : u ∈ orIn n C q ∨ v ∈ orIn n C q
        · left
          rcases hz with rfl | rfl
          · by_cases hup : z ∈ orIn n C p
            · have hvq : v ∈ orIn n C q := by
                rcases hRq with h | h
                · exact absurd h (fun h' => hdisj z hup h')
                · exact h
              exact ⟨X, hX, Y, hY, A, Q, p, q, z, v, hcone, hop, hin, hYop, Or.inl hpq, hYr,
                Or.inl ⟨rfl, rfl⟩, hzA, hup, hvq⟩
            · have hvp : v ∈ orIn n C p := by
                rcases hRp with h | h
                · exact absurd h hup
                · exact h
              have huq : z ∈ orIn n C q := by
                rcases hRq with h | h
                · exact h
                · exact absurd h (fun h' => hdisj v hvp h')
              exact ⟨X, hX, Y, hY, A, Q, q, p, z, v, hcone, hop, hin, hYop, Or.inr hpq, hYr,
                Or.inl ⟨rfl, rfl⟩, hzA, huq, hvp⟩
          · by_cases hvp : z ∈ orIn n C p
            · have huq : u ∈ orIn n C q := by
                rcases hRq with h | h
                · exact h
                · exact absurd h (fun h' => hdisj z hvp h')
              exact ⟨X, hX, Y, hY, A, Q, p, q, z, u, hcone, hop, hin, hYop, Or.inl hpq, hYr,
                Or.inr ⟨rfl, rfl⟩, hzA, hvp, huq⟩
            · have hup : u ∈ orIn n C p := by
                rcases hRp with h | h
                · exact h
                · exact absurd h hvp
              have hvq : z ∈ orIn n C q := by
                rcases hRq with h | h
                · exact absurd h (fun h' => hdisj u hup h')
                · exact h
              exact ⟨X, hX, Y, hY, A, Q, q, p, z, u, hcone, hop, hin, hYop, Or.inr hpq, hYr,
                Or.inr ⟨rfl, rfl⟩, hzA, hvq, hup⟩
        · push_neg at hRq
          obtain ⟨z', hz', hz'p⟩ : ∃ z' : Fin n, (z' = u ∨ z' = v) ∧ z' ∈ orIn n C p := by
            rcases hRp with h | h
            · exact ⟨u, Or.inl rfl, h⟩
            · exact ⟨v, Or.inr rfl, h⟩
          exact ih Y hYX hY hYcone hYop hYv p q z' (Or.inl hpq) hz' hz'p hRq.1 hRq.2
      · push_neg at hRp
        by_cases hRq : u ∈ orIn n C q ∨ v ∈ orIn n C q
        · obtain ⟨z', hz', hz'q⟩ : ∃ z' : Fin n, (z' = u ∨ z' = v) ∧ z' ∈ orIn n C q := by
            rcases hRq with h | h
            · exact ⟨u, Or.inl rfl, h⟩
            · exact ⟨v, Or.inr rfl, h⟩
          exact ih Y hYX hY hYcone hYop hYv q p z' (Or.inr hpq) hz' hz'q hRp.1 hRp.2
        · push_neg at hRq
          right
          exact ⟨Y, hY, p, q, hYcone, hYop, hpq, hYv, hRp.1, hRp.2, hRq.1, hRq.2⟩
    · exfalso
      have hiuv : i = u ∨ i = v := by simpa [pairInput] using hiv
      rcases hiuv with rfl | rfl
      · exact huQ hiQ
      · exact hvQ hiQ

theorem main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO2 : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hone : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ∀ t : Fin n, gateVal n C k (fun r => decide (r = t)) = false)
    (u v : Fin n) (o : ℕ) (hadj : G.Adj u v) (hout : C.output = n + o)
    (hrt : ReadTwiceAt n C o u v) : Pat1 n C u v ∨ Pat2 n C u v := by
  have huv : u ≠ v := hadj.ne
  have huv' : (u : ℕ) ≠ (v : ℕ) := fun h => huv (Fin.ext h)
  have hAO2' := hAO2
  obtain ⟨hAO, hRB, h2⟩ := hAO2'
  have hcirc : ∀ y : Fin n → Bool, circuitFun n C y = W n C y (n + o) := by
    intro y
    simp only [circuitFun, Circuit.eval, W, hout]
  have hox : W n C (pairInput u v) (n + o) = true := by
    rw [← hcirc, hfun]
    simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inr ⟨u, v, hadj, by simp [pairInput], by simp [pairInput]⟩
  have hnone : ∀ t : Fin n, graphFun G ∅ (fun r => decide (r = t)) = false := by
    intro t
    simp only [graphFun, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    refine ⟨by simp, ?_⟩
    rintro ⟨a, b, hab, ha, hb⟩
    simp only [decide_eq_true_eq] at ha hb
    exact hab.ne (ha.trans hb.symm)
  rcases descent n C hAO _ (n + o) hox with ⟨X, hXr, hXop, hXv⟩ | ⟨i, hio, hiv⟩
  · obtain ⟨_, hol, hXle⟩ := orReach_bound n C (n + o) X hXr
    have ho : o < C.gates.length := by omega
    have hX : X < C.gates.length := by omega
    have hXcone : InOutputCone n C X := by
      rcases orReach_cone n C o ho X hXr with h | h
      · exact ⟨hX, Or.inl (by rw [hout, h])⟩
      · exact ⟨hX, Or.inr ⟨by omega, by rw [hout, show n + o - n = o by omega]; exact h⟩⟩
    obtain ⟨a, b, hab⟩ := two_inputs n C h2 X hX
    have ha_lt : a < n + X := hRB X hX a (by rw [hab]; simp)
    have hb_lt : b < n + X := hRB X hX b (by rw [hab]; simp)
    have hdisj := and_disjoint n C hone X hX hXop a b hab ha_lt hb_lt
    by_cases hRa : u ∈ orIn n C a ∨ v ∈ orIn n C a
    · by_cases hRb : u ∈ orIn n C b ∨ v ∈ orIn n C b
      · exfalso
        have hvec : [1, 1] ∈ (readVectors C n [(u : ℕ), (v : ℕ)] 1).getD (n + X) [] := by
          by_cases hua : u ∈ orIn n C a
          · have hvb : v ∈ orIn n C b := by
              rcases hRb with h | h
              · exact absurd h (fun h' => hdisj u hua h')
              · exact h
            have := rv_and n C [(u : ℕ), (v : ℕ)] 1 X hX hXop a b hab ha_lt hb_lt [1, 0] [0, 1]
              (rv_orIn n C hRB _ 1 _ a u (leaf_u _ _ huv') hua)
              (rv_orIn n C hRB _ 1 _ b v (leaf_v _ _ huv') hvb)
            have e1 : ([(u : ℕ), (v : ℕ)].map fun _ => (0 : ℕ)) = [0, 0] := rfl
            have e2 : capAdd 1 (capAdd 1 [0, 0] [1, 0]) [0, 1] = [1, 1] := by decide
            rw [e1, e2] at this
            exact this
          · have hva : v ∈ orIn n C a := by
              rcases hRa with h | h
              · exact absurd h hua
              · exact h
            have hub : u ∈ orIn n C b := by
              rcases hRb with h | h
              · exact h
              · exact absurd h (fun h' => hdisj v hva h')
            have := rv_and n C [(u : ℕ), (v : ℕ)] 1 X hX hXop a b hab ha_lt hb_lt [0, 1] [1, 0]
              (rv_orIn n C hRB _ 1 _ a v (leaf_v _ _ huv') hva)
              (rv_orIn n C hRB _ 1 _ b u (leaf_u _ _ huv') hub)
            have e1 : ([(u : ℕ), (v : ℕ)].map fun _ => (0 : ℕ)) = [0, 0] := rfl
            have e2 : capAdd 1 (capAdd 1 [0, 0] [0, 1]) [1, 0] = [1, 1] := by decide
            rw [e1, e2] at this
            exact this
        have htop := rv_orReach n C [(u : ℕ), (v : ℕ)] 1 [1, 1] (n + o) X hXr hvec
        have hgood : readsAtMost (atGate n C o) n [(u : ℕ), (v : ℕ)] 1 = true := by
          have hrv : readVectors (atGate n C o) n [(u : ℕ), (v : ℕ)] 1 =
              readVectors C n [(u : ℕ), (v : ℕ)] 1 := rfl
          have hao : (atGate n C o).output = n + o := rfl
          unfold readsAtMost
          rw [hrv, hao]
          exact List.any_eq_true.mpr ⟨[1, 1], htop, by decide⟩
        have hrt' : readsAtMost (atGate n C o) n [(u : ℕ), (v : ℕ)] 1 = false := hrt
        rw [hrt'] at hgood
        exact Bool.false_ne_true hgood
      · push_neg at hRb
        obtain ⟨z, hz, hza⟩ : ∃ z : Fin n, (z = u ∨ z = v) ∧ z ∈ orIn n C a := by
          rcases hRa with h | h
          · exact ⟨u, Or.inl rfl, h⟩
          · exact ⟨v, Or.inr rfl, h⟩
        exact half_descend n C hAO2 hone u v X hX hXcone hXop hXv a b z (Or.inl hab) hz hza
          hRb.1 hRb.2
    · push_neg at hRa
      by_cases hRb : u ∈ orIn n C b ∨ v ∈ orIn n C b
      · obtain ⟨z, hz, hzb⟩ : ∃ z : Fin n, (z = u ∨ z = v) ∧ z ∈ orIn n C b := by
          rcases hRb with h | h
          · exact ⟨u, Or.inl rfl, h⟩
          · exact ⟨v, Or.inr rfl, h⟩
        exact half_descend n C hAO2 hone u v X hX hXcone hXop hXv b a z (Or.inr hab) hz hzb
          hRa.1 hRa.2
      · push_neg at hRb
        right
        exact ⟨X, hX, a, b, hXcone, hXop, hab, hXv, hRa.1, hRa.2, hRb.1, hRb.2⟩
  · exfalso
    have hi1 : W n C (fun r => decide (r = i)) (n + o) = true :=
      orIn_val n C (fun r => decide (r = i)) (n + o) i hio (by simp)
    rw [← hcirc, hfun, hnone i] at hi1
    exact Bool.false_ne_true hi1

end PEqualNP.Outside.L_meta_3756

theorem PEqualNP.Outside.L_meta_3756 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t : Fin n, PEqualNP.EdgeOwnership.gateVal n C k (fun r => decide (r = t)) = false) → ∀ (u v : Fin n) (o : ℕ), G.Adj u v → C.output = n + o → PEqualNP.Core.ReadTwiceAt n C o u v → (∃ X < C.gates.length, ∃ Y < C.gates.length, ∃ (A Q P N : ℕ) (z w : Fin n), PEqualNP.Core.InOutputCone n C X ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C X).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C X).inputs = [A, Q] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C X).inputs = [Q, A]) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C Y).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C Y).inputs = [P, N] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C Y).inputs = [N, P]) ∧ PEqualNP.CleanedNonEdge.OrReaches n C Q Y ∧ ((z = u ∧ w = v) ∨ (z = v ∧ w = u)) ∧ z ∈ PEqualNP.TopForm.orIn n C A ∧ z ∈ PEqualNP.TopForm.orIn n C P ∧ w ∈ PEqualNP.TopForm.orIn n C N) ∨ (∃ W < C.gates.length, ∃ L M : ℕ, PEqualNP.Core.InOutputCone n C W ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C W).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C W).inputs = [L, M] ∧ PEqualNP.EdgeOwnership.gateVal n C W (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ u ∉ PEqualNP.TopForm.orIn n C L ∧ v ∉ PEqualNP.TopForm.orIn n C L ∧ u ∉ PEqualNP.TopForm.orIn n C M ∧ v ∉ PEqualNP.TopForm.orIn n C M) := by
  intro n G _ C hAO2 hfun hone u v o hadj hout hrt
  exact PEqualNP.Outside.L_meta_3756.main n G C hAO2 hfun hone u v o hadj hout hrt
