import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5562

noncomputable section Checker

def neg (l : Nat) : Nat :=
  match Nat.beq (Nat.mod l (nat_lit 2)) (nat_lit 0) with
  | true => Nat.add l (nat_lit 1)
  | false => Nat.sub l (nat_lit 1)

def bit (T l : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight T l) (nat_lit 1)) (nat_lit 1)

def setBit (T u : Nat) : Nat := Nat.lor T (Nat.shiftLeft (nat_lit 1) u)

theorem bit_eq_testBit (T l : Nat) : bit T l = T.testBit l := by
  have h : Nat.land (Nat.shiftRight T l) 1 = (T >>> l) % 2 := Nat.and_one_is_mod _
  unfold bit
  rw [h, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, Bool.eq_iff_iff,
    decide_eq_true_eq]
  exact ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl _⟩

theorem bit_setBit (T u l : Nat) : bit (setBit T u) l = (bit T l || decide (u = l)) := by
  have h : setBit T u = T ||| (1 <<< u) := rfl
  rw [h, bit_eq_testBit, bit_eq_testBit, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

def litVal (a : Nat → Bool) (l : Nat) : Bool := a (l / 2) == (l % 2 == 0)

def ClauseSat (a : Nat → Bool) (c : List Nat) : Prop := ∃ l ∈ c, litVal a l = true

def FormulaSat (F : List (List Nat)) : Prop := ∃ a : Nat → Bool, ∀ c ∈ F, ClauseSat a c

theorem litVal_neg (a : Nat → Bool) (l : Nat) : litVal a (neg l) = !litVal a l := by
  have hn : neg l = if l % 2 = 0 then l + 1 else l - 1 := by
    unfold neg
    cases hb : Nat.beq (Nat.mod l 2) 0 with
    | false =>
      have h1 : ¬ (l % 2 = 0) := Nat.ne_of_beq_eq_false hb
      rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]; rfl
    | true =>
      have h1 : l % 2 = 0 := Nat.eq_of_beq_eq_true hb
      rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
  rw [hn]
  unfold litVal
  by_cases h : l % 2 = 0
  · have h1 : (l + 1) / 2 = l / 2 := by omega
    have h2 : (l + 1) % 2 = 1 := by omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true h), h1, h2, h]
    cases a (l / 2) <;> rfl
  · have h1 : (l - 1) / 2 = l / 2 := by omega
    have h2 : (l - 1) % 2 = 0 := by omega
    have h3 : l % 2 = 1 := by omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false h), h1, h2, h3]
    cases a (l / 2) <;> rfl

def tget (t : BinaryTree (Option Nat)) : Nat → Option Nat :=
  BinaryTree.rec (motive := fun _ => Nat → Option Nat) (fun _ => none)
    (fun v _ _ ihl ihr k =>
      Bool.rec
        (Bool.rec (ihr (Nat.sub (Nat.div k (nat_lit 2)) (nat_lit 1))) (ihl (Nat.div k (nat_lit 2)))
          (Nat.beq (Nat.mod k (nat_lit 2)) (nat_lit 1)))
        v (Nat.beq k (nat_lit 0))) t

def troot (t : BinaryTree (Option Nat)) : Option Nat :=
  BinaryTree.rec (motive := fun _ => Option Nat) none (fun v _ _ _ _ => v) t

def tleft (t : BinaryTree (Option Nat)) : BinaryTree (Option Nat) :=
  BinaryTree.rec (motive := fun _ => BinaryTree (Option Nat)) BinaryTree.nil (fun _ l _ _ _ => l) t

def tright (t : BinaryTree (Option Nat)) : BinaryTree (Option Nat) :=
  BinaryTree.rec (motive := fun _ => BinaryTree (Option Nat)) BinaryTree.nil (fun _ _ r _ _ => r) t

def tset (fuel : Nat) : BinaryTree (Option Nat) → Nat → Option Nat → BinaryTree (Option Nat) :=
  Nat.rec (motive := fun _ => BinaryTree (Option Nat) → Nat → Option Nat → BinaryTree (Option Nat))
    (fun t _ _ => t)
    (fun _ ih t k o =>
      Bool.rec
        (Bool.rec
          (BinaryTree.node (troot t) (tleft t)
            (ih (tright t) (Nat.sub (Nat.div k (nat_lit 2)) (nat_lit 1)) o))
          (BinaryTree.node (troot t) (ih (tleft t) (Nat.div k (nat_lit 2)) o) (tright t))
          (Nat.beq (Nat.mod k (nat_lit 2)) (nat_lit 1)))
        (BinaryTree.node o (tleft t) (tright t)) (Nat.beq k (nat_lit 0))) fuel

def TAll (P : Nat → Prop) : BinaryTree (Option Nat) → Prop
  | BinaryTree.nil => True
  | BinaryTree.node v l r => (∀ c, v = some c → P c) ∧ TAll P l ∧ TAll P r

theorem TAll.get {P : Nat → Prop} :
    ∀ {t : BinaryTree (Option Nat)} {k : Nat} {c : Nat}, TAll P t → tget t k = some c → P c
  | BinaryTree.nil, _, _, _, h => by simp [tget] at h
  | BinaryTree.node v l r, k, c, ⟨hv, hl, hr⟩, h => by
    change Bool.rec (Bool.rec (tget r _) (tget l _) _) v _ = some c at h
    cases h0 : Nat.beq k 0
    · rw [h0] at h
      cases h1 : Nat.beq (Nat.mod k 2) 1
      · rw [h1] at h; exact TAll.get hr h
      · rw [h1] at h; exact TAll.get hl h
    · rw [h0] at h; exact hv c h

theorem TAll.root {P : Nat → Prop} {t : BinaryTree (Option Nat)} (h : TAll P t) :
    ∀ c, troot t = some c → P c := by
  cases t with
  | nil => intro c hc; cases hc
  | node v l r => exact h.1

theorem TAll.left {P : Nat → Prop} {t : BinaryTree (Option Nat)} (h : TAll P t) :
    TAll P (tleft t) := by
  cases t with
  | nil => trivial
  | node v l r => exact h.2.1

theorem TAll.right {P : Nat → Prop} {t : BinaryTree (Option Nat)} (h : TAll P t) :
    TAll P (tright t) := by
  cases t with
  | nil => trivial
  | node v l r => exact h.2.2

theorem TAll.set {P : Nat → Prop} :
    ∀ (fuel : Nat) {t : BinaryTree (Option Nat)} (k : Nat) {o : Option Nat},
      TAll P t → (∀ c, o = some c → P c) → TAll P (tset fuel t k o)
  | 0, _, _, _, ht, _ => ht
  | fuel + 1, t, k, o, ht, ho => by
    change TAll P (Bool.rec (Bool.rec
      (BinaryTree.node (troot t) (tleft t) (tset fuel (tright t) _ o))
      (BinaryTree.node (troot t) (tset fuel (tleft t) _ o) (tright t)) _)
      (BinaryTree.node o (tleft t) (tright t)) _)
    cases h0 : Nat.beq k 0
    · cases h1 : Nat.beq (Nat.mod k 2) 1
      · exact ⟨ht.root, ht.left, TAll.set fuel _ ht.right ho⟩
      · exact ⟨ht.root, TAll.set fuel _ ht.left ho, ht.right⟩
    · exact ⟨ho, ht.left, ht.right⟩

theorem bit_land (x y l : Nat) : bit (Nat.land x y) l = (bit x l && bit y l) := by
  rw [bit_eq_testBit, bit_eq_testBit, bit_eq_testBit]
  exact Nat.testBit_and x y l

theorem bit_xor (x y l : Nat) : bit (Nat.xor x y) l = (bit x l ^^ bit y l) := by
  rw [bit_eq_testBit, bit_eq_testBit, bit_eq_testBit]
  exact Nat.testBit_xor x y l

theorem bit_zero (l : Nat) : bit 0 l = false := by
  rw [bit_eq_testBit]; exact Nat.zero_testBit l

theorem bit_pow (u l : Nat) : bit (Nat.shiftLeft 1 u) l = decide (u = l) := by
  have h : Nat.shiftLeft 1 u = 1 <<< u := rfl
  rw [bit_eq_testBit, h, Nat.one_shiftLeft, Nat.testBit_two_pow]

def mask : List Nat → Nat
  | [] => 0
  | l :: ls => setBit (mask ls) l

theorem bit_mask : ∀ (c : List Nat) (l : Nat), bit (mask c) l = true ↔ l ∈ c
  | [], l => by simp [mask, bit_zero]
  | x :: xs, l => by
    rw [mask, bit_setBit, Bool.or_eq_true, bit_mask xs l, decide_eq_true_eq, List.mem_cons]
    exact ⟨fun h => h.elim Or.inr (fun h => Or.inl h.symm),
      fun h => h.elim (fun h => Or.inr h.symm) Or.inl⟩

abbrev Cont := BinaryTree (Option Nat) → Nat → Bool → Nat → Nat → Nat → Bool

def stepRead (k : Cont) (db : BinaryTree (Option Nat)) (id C F P x : Nat) : Bool :=
  Bool.rec
    (Bool.rec (k db id false (setBit C x) F P) (k db id true C C 0) (Nat.beq x (nat_lit 0)))
    (k db (Nat.succ x) false C F P)
    (Nat.beq id (nat_lit 0))

def stepUnit (k : Cont) (db : BinaryTree (Option Nat)) (id C F P x : Nat) : Bool :=
  Bool.rec false (k db id true C (setBit F (neg x)) 0) (Nat.beq P (Nat.shiftLeft (nat_lit 1) x))

def lg (U : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun lo _ => lo)
    (fun _ ih lo hi =>
      Bool.rec (ih (Nat.div (Nat.add lo hi) (nat_lit 2)) hi)
        (ih lo (Nat.div (Nat.add lo hi) (nat_lit 2)))
        (Nat.beq (Nat.shiftRight U (Nat.div (Nat.add lo hi) (nat_lit 2))) (nat_lit 0)))
    (nat_lit 17) (nat_lit 0) (nat_lit 65536)

def stepU (k : Cont) (db : BinaryTree (Option Nat)) (id C F U : Nat) : Bool :=
  Bool.rec false (k db id true C (setBit F (neg (lg U))) 0)
    (Nat.beq U (Nat.shiftLeft (nat_lit 1) (lg U)))

def stepClause (k : Cont) (db : BinaryTree (Option Nat)) (id C F D : Nat) : Bool :=
  Bool.rec (stepU k db id C F (Nat.xor D (Nat.land D F)))
    (Bool.rec (k (tset 64 db (Nat.sub id (nat_lit 1)) (some C)) 0 false 0 0 0) true
      (Nat.beq C (nat_lit 0)))
    (Nat.beq (Nat.xor D (Nat.land D F)) (nat_lit 0))

def stepHint (k : Cont) (db : BinaryTree (Option Nat)) (id C F x : Nat) : Bool :=
  Option.rec false (stepClause k db id C F) (tget db x)

def tokenStep (k : Cont) (x : Nat) : Cont := fun db id mode C F P =>
  Bool.rec (stepRead k db id C F P x)
    (Bool.rec (stepUnit k db id C F P x) (stepHint k db id C F x) (Nat.beq P (nat_lit 0)))
    mode

def stop : Cont := fun _ _ _ _ _ _ => false

def runS (e : Cont) (toks : List Nat) : Cont :=
  List.rec (motive := fun _ => Cont) e (fun x _ k => tokenStep k x) toks

def runWord (W M fuel w : Nat) (k : Cont) : Cont :=
  Nat.rec (motive := fun _ => Nat → Cont) (fun _ => k)
    (fun _ ih w =>
      Bool.rec (tokenStep (ih (Nat.shiftRight w W)) (Nat.land w M)) k (Nat.beq w (nat_lit 1)))
    fuel w

def fuelW : Nat := 1024

def keysOf (bits : Nat) (m : Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → List Nat) (fun _ _ => [])
    (fun _ ih i c =>
      Bool.rec (0 :: ih (Nat.succ i) c) (Nat.succ c :: ih (Nat.succ i) (Nat.succ c)) (bit bits i))
    m 0 0

def runW (e : Cont) (W : Nat) (words : List Nat) : Cont :=
  List.rec (motive := fun _ => Cont) e
    (fun w _ k => runWord W (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1)) fuelW w k) words

def entryIn (db : BinaryTree (Option Nat)) (e : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun q lits _ =>
      Option.rec false (fun D => Nat.beq D (mask lits)) (tget db (Nat.sub q (nat_lit 1)))) e

def verify (B : List (List Nat)) : Cont := fun db _ _ _ _ _ =>
  List.rec (motive := fun _ => Bool) true (fun e _ ih => Bool.rec false ih (entryIn db e)) B

def loadF : List (List Nat) → List Nat → BinaryTree (Option Nat) → BinaryTree (Option Nat)
  | [], _, t => t
  | _ :: _, [], t => t
  | c :: cs, q :: qs, t =>
    loadF cs qs (Bool.rec (tset 64 t (Nat.sub q 1) (some (mask c))) t (Nat.beq q 0))

def loadB : List (List Nat) → BinaryTree (Option Nat) → BinaryTree (Option Nat)
  | [], t => t
  | [] :: es, t => loadB es t
  | (q :: lits) :: es, t => loadB es (tset 64 t (Nat.sub q 1) (some (mask lits)))

def check (F : List (List Nat)) (fk : List Nat) (toks : List Nat) : Bool :=
  runS stop toks (loadF F fk BinaryTree.nil) 0 false 0 0 0

def checkW (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat) : Bool :=
  runW stop W words (loadF F fk BinaryTree.nil) 0 false 0 0 0

def checkFirst (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat)
    (B : List (List Nat)) : Bool :=
  runW (verify B) W words (loadF F fk BinaryTree.nil) 0 false 0 0 0

def checkSeg (B : List (List Nat)) (W : Nat) (words : List Nat) (B' : List (List Nat)) : Bool :=
  runW (verify B') W words (loadB B BinaryTree.nil) 0 false 0 0 0

def checkLast (B : List (List Nat)) (W : Nat) (words : List Nat) : Bool :=
  runW stop W words (loadB B BinaryTree.nil) 0 false 0 0 0

section Soundness

variable (a : Nat → Bool)

def MaskSat (m : Nat) : Prop := ∃ l, bit m l = true ∧ litVal a l = true

def BitsFalse (F : Nat) : Prop := ∀ l, bit F l = true → litVal a l = false

def EntriesSat (B : List (List Nat)) : Prop := ∀ e ∈ B, ClauseSat a e.tail

def HintInv (C F P : Nat) : Prop :=
  (∀ x, bit C x = true → litVal a x = false) →
    BitsFalse a F ∧ (P = 0 ∨ ∃ w, bit P w = true ∧ litVal a w = true)

theorem witness_U {F D : Nat} (hF : BitsFalse a F) (hD : MaskSat a D) :
    ∃ w, bit (Nat.xor D (Nat.land D F)) w = true ∧ litVal a w = true := by
  obtain ⟨w, hwD, hwv⟩ := hD
  have hwF : bit F w = false := by
    cases hb : bit F w
    · rfl
    · rw [hF w hb] at hwv; exact absurd hwv (by simp)
  exact ⟨w, by rw [bit_xor, bit_land, hwD, hwF]; rfl, hwv⟩

def Good (Q : Prop) (k : Cont) : Prop :=
  ∀ db id mode C F P, TAll (MaskSat a) db → (mode = true → HintInv a C F P) →
    k db id mode C F P = true → Q

theorem stop_good (Q : Prop) : Good a Q stop := by
  intro _ _ _ _ _ _ _ _ h
  exact absurd h (by simp [stop])

theorem tokenStep_good {Q : Prop} {k : Cont} (hk : Good a Q k) (x : Nat) :
    Good a Q (tokenStep k x) := by
  intro db id mode C F P hdb hinv h
  change Bool.rec (stepRead k db id C F P x)
    (Bool.rec (stepUnit k db id C F P x) (stepHint k db id C F x) (Nat.beq P 0)) mode = true at h
  cases mode with
  | false =>
    change Bool.rec
      (Bool.rec (k db id false (setBit C x) F P) (k db id true C C 0) (Nat.beq x 0))
      (k db (Nat.succ x) false C F P) (Nat.beq id 0) = true at h
    cases hi : Nat.beq id 0
    · rw [hi] at h
      cases hx : Nat.beq x 0
      · rw [hx] at h
        exact hk db id false _ F P hdb (by simp) h
      · rw [hx] at h
        exact hk db id true C C 0 hdb (fun _ hC => ⟨hC, Or.inl rfl⟩) h
    · rw [hi] at h
      exact hk db _ false C F P hdb (by simp) h
  | true =>
    have hinv := hinv rfl
    cases hP : Nat.beq P 0
    · rw [hP] at h
      change Bool.rec false (k db id true C (setBit F (neg x)) 0)
        (Nat.beq P (Nat.shiftLeft 1 x)) = true at h
      cases hu : Nat.beq P (Nat.shiftLeft 1 x)
      · rw [hu] at h; exact absurd h (by simp)
      · rw [hu] at h
        refine hk db id true C _ 0 hdb (fun _ hC => ⟨?_, Or.inl rfl⟩) h
        obtain ⟨hF, hPw⟩ := hinv hC
        rcases hPw with hP0 | ⟨w, hw, hwv⟩
        · rw [hP0] at hP; exact absurd hP (by simp)
        · rw [Nat.eq_of_beq_eq_true hu, bit_pow, decide_eq_true_eq] at hw
          subst hw
          intro l hl
          rw [bit_setBit, Bool.or_eq_true, decide_eq_true_eq] at hl
          rcases hl with hl | rfl
          · exact hF l hl
          · rw [litVal_neg, hwv]; rfl
    · rw [hP] at h
      change Option.rec false (stepClause k db id C F) (tget db x) = true at h
      cases hg : tget db x with
      | none => rw [hg] at h; exact absurd h (by simp)
      | some D =>
        rw [hg] at h
        have hD : MaskSat a D := TAll.get hdb hg
        change Bool.rec (stepU k db id C F (Nat.xor D (Nat.land D F)))
          (Bool.rec (k (tset 64 db (Nat.sub id 1) (some C)) 0 false 0 0 0) true
            (Nat.beq C 0))
          (Nat.beq (Nat.xor D (Nat.land D F)) 0) = true at h
        cases hU : Nat.beq (Nat.xor D (Nat.land D F)) 0
        · rw [hU] at h
          change Bool.rec false
            (k db id true C (setBit F (neg (lg (Nat.xor D (Nat.land D F))))) 0)
            (Nat.beq (Nat.xor D (Nat.land D F)) (Nat.shiftLeft 1 (lg (Nat.xor D (Nat.land D F)))))
            = true at h
          cases hu : Nat.beq (Nat.xor D (Nat.land D F))
              (Nat.shiftLeft 1 (lg (Nat.xor D (Nat.land D F))))
          · rw [hu] at h; exact absurd h (by simp)
          · rw [hu] at h
            refine hk db id true C _ 0 hdb (fun _ hC => ⟨?_, Or.inl rfl⟩) h
            obtain ⟨w, hw, hwv⟩ := witness_U a (hinv hC).1 hD
            rw [Nat.eq_of_beq_eq_true hu, bit_pow, decide_eq_true_eq] at hw
            subst hw
            intro l hl
            rw [bit_setBit, Bool.or_eq_true, decide_eq_true_eq] at hl
            rcases hl with hl | rfl
            · exact (hinv hC).1 l hl
            · rw [litVal_neg, hwv]; rfl
        · rw [hU] at h

          have hCsat : MaskSat a C := by
            apply Classical.byContradiction
            intro hn
            have hC : ∀ y, bit C y = true → litVal a y = false := by
              intro y hy
              cases hv : litVal a y
              · rfl
              · exact absurd ⟨y, hy, hv⟩ hn
            obtain ⟨w, hw, _⟩ := witness_U a (hinv hC).1 hD
            rw [Nat.eq_of_beq_eq_true hU, bit_zero] at hw
            exact absurd hw (by simp)
          cases hC0 : Nat.beq C 0
          · rw [hC0] at h
            exact hk _ _ false 0 0 0
              (TAll.set 64 _ hdb (fun c hc => by cases hc; exact hCsat)) (by simp) h
          · obtain ⟨w, hw, _⟩ := hCsat
            rw [Nat.eq_of_beq_eq_true hC0, bit_zero] at hw
            exact absurd hw (by simp)

theorem runS_good {Q : Prop} {e : Cont} (he : Good a Q e) :
    ∀ toks : List Nat, Good a Q (runS e toks)
  | [] => he
  | x :: xs => tokenStep_good a (runS_good he xs) x

theorem runWord_good {Q : Prop} (W M : Nat) {k : Cont} (hk : Good a Q k) :
    ∀ fuel w, Good a Q (runWord W M fuel w k)
  | 0, _ => hk
  | fuel + 1, w => by
    change Good a Q (Bool.rec (tokenStep (runWord W M fuel (Nat.shiftRight w W) k)
      (Nat.land w M)) k (Nat.beq w 1))
    cases Nat.beq w 1
    · exact tokenStep_good a (runWord_good W M hk fuel _) _
    · exact hk

theorem runW_good {Q : Prop} {e : Cont} (he : Good a Q e) (W : Nat) :
    ∀ words : List Nat, Good a Q (runW e W words)
  | [] => he
  | w :: ws => by
    have h := runWord_good a W (Nat.sub (Nat.shiftLeft 1 W) 1) (runW_good he W ws) fuelW w
    exact h

theorem clauseSat_of_maskSat {c : List Nat} (h : MaskSat a (mask c)) : ClauseSat a c := by
  obtain ⟨l, hl, hv⟩ := h
  exact ⟨l, (bit_mask c l).mp hl, hv⟩

theorem maskSat_of_clauseSat {c : List Nat} (h : ClauseSat a c) : MaskSat a (mask c) := by
  obtain ⟨l, hl, hv⟩ := h
  exact ⟨l, (bit_mask c l).mpr hl, hv⟩

theorem verify_good (B : List (List Nat)) : Good a (EntriesSat a B) (verify B) := by
  intro db _ _ _ _ _ hdb _ h
  induction B with
  | nil => intro e he; simp at he
  | cons e es ih =>
    change Bool.rec false (List.rec (motive := fun _ => Bool) true
      (fun e _ ih => Bool.rec false ih (entryIn db e)) es) (entryIn db e) = true at h
    cases he : entryIn db e
    · rw [he] at h; exact absurd h (by simp)
    · rw [he] at h
      intro e' he'
      rcases List.mem_cons.mp he' with rfl | he'
      · cases e' with
        | nil => simp [entryIn] at he
        | cons q lits =>
          change Option.rec false (fun D => Nat.beq D (mask lits)) (tget db (Nat.sub q 1)) = true
            at he
          cases hg : tget db (Nat.sub q 1) with
          | none => rw [hg] at he; exact absurd he (by simp)
          | some D =>
            rw [hg] at he
            have hD := TAll.get hdb hg
            rw [Nat.eq_of_beq_eq_true he] at hD
            exact clauseSat_of_maskSat a hD
      · exact ih h e' he'

theorem loadF_all : ∀ (F : List (List Nat)) (fk : List Nat) {t : BinaryTree (Option Nat)}, TAll (MaskSat a) t →
    (∀ c ∈ F, ClauseSat a c) → TAll (MaskSat a) (loadF F fk t)
  | [], _, _, ht, _ => ht
  | _ :: _, [], _, ht, _ => ht
  | c :: cs, q :: qs, t, ht, hF => by
    unfold loadF
    apply loadF_all cs qs _ (fun c' hc' => hF c' (List.mem_cons_of_mem _ hc'))
    cases Nat.beq q 0
    · exact TAll.set 64 _ ht (fun c' hc' => by
        cases hc'; exact maskSat_of_clauseSat a (hF c List.mem_cons_self))
    · exact ht

theorem loadB_all : ∀ (B : List (List Nat)) {t : BinaryTree (Option Nat)}, TAll (MaskSat a) t →
    EntriesSat a B → TAll (MaskSat a) (loadB B t)
  | [], _, ht, _ => ht
  | [] :: es, _, ht, hB => loadB_all es ht (fun e he => hB e (List.mem_cons_of_mem _ he))
  | (q :: lits) :: es, t, ht, hB => by
    unfold loadB
    apply loadB_all es _ (fun e he => hB e (List.mem_cons_of_mem _ he))
    exact TAll.set 64 _ ht (fun c' hc' => by
      cases hc'; exact maskSat_of_clauseSat a (hB _ List.mem_cons_self))

end Soundness

theorem check_sound (F : List (List Nat)) (fk toks : List Nat) (h : check F fk toks = true) :
    ¬ FormulaSat F := by
  rintro ⟨a, ha⟩
  exact runS_good a (stop_good a False) toks _ _ false 0 0 0
    (loadF_all a F fk (t := BinaryTree.nil) trivial ha) (by simp) h

theorem checkW_sound (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat)
    (h : checkW F fk W words = true) : ¬ FormulaSat F := by
  rintro ⟨a, ha⟩
  exact runW_good a (stop_good a False) W words _ _ false 0 0 0
    (loadF_all a F fk (t := BinaryTree.nil) trivial ha) (by simp) h

theorem checkFirst_sound (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat)
    (B : List (List Nat)) (h : checkFirst F fk W words B = true) :
    ∀ a, (∀ c ∈ F, ClauseSat a c) → EntriesSat a B := fun a ha =>
  runW_good a (verify_good a B) W words _ _ false 0 0 0
    (loadF_all a F fk (t := BinaryTree.nil) trivial ha) (by simp) h

theorem checkSeg_sound (B : List (List Nat)) (W : Nat) (words : List Nat) (B' : List (List Nat))
    (h : checkSeg B W words B' = true) : ∀ a, EntriesSat a B → EntriesSat a B' := fun a hB =>
  runW_good a (verify_good a B') W words _ _ false 0 0 0
    (loadB_all a B (t := BinaryTree.nil) trivial hB) (by simp) h

theorem checkLast_sound (B : List (List Nat)) (W : Nat) (words : List Nat)
    (h : checkLast B W words = true) : ∀ a, EntriesSat a B → False := fun a hB =>
  runW_good a (stop_good a False) W words _ _ false 0 0 0
    (loadB_all a B (t := BinaryTree.nil) trivial hB) (by simp) h

def unpackWord (W M fuel w : Nat) (rest : List Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => rest)
    (fun _ ih w => Bool.rec (Nat.land w M :: ih (Nat.shiftRight w W)) rest (Nat.beq w (nat_lit 1)))
    fuel w

def unpack (W : Nat) (words : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun w _ ih => unpackWord W (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1)) 1024 w ih)
    words

def decodeF (toks : List Nat) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) []
    (fun x _ acc =>
      Bool.rec (List.rec (motive := fun _ => List (List Nat)) [[x]] (fun c cs _ => (x :: c) :: cs) acc)
        ([] :: acc) (Nat.beq x (nat_lit 0)))
    toks

end Checker

section Shannon

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

end Shannon

namespace Lk

def Model : Type := (ℕ → ℕ) × (ℕ → ℕ) × (ℕ → ℕ) × ℕ × (ℕ → ℕ → Bool)

def Model.mk (op s1 s2 : ℕ → ℕ) (so : ℕ) (w : ℕ → ℕ → Bool) : Model := (op, s1, s2, so, w)

def Model.op (M : Model) : ℕ → ℕ := Prod.fst M

def Model.s1 (M : Model) : ℕ → ℕ := Prod.fst (Prod.snd M)

def Model.s2 (M : Model) : ℕ → ℕ := Prod.fst (Prod.snd (Prod.snd M))

def Model.so (M : Model) : ℕ := Prod.fst (Prod.snd (Prod.snd (Prod.snd M)))

def Model.w (M : Model) : ℕ → ℕ → Bool := Prod.snd (Prod.snd (Prod.snd (Prod.snd M)))

section mklemmas
variable (op s1 s2 : ℕ → ℕ) (so : ℕ) (w : ℕ → ℕ → Bool)
theorem op_mk (j : ℕ) : (Model.mk op s1 s2 so w).op j = op j := rfl
theorem s1_mk (j : ℕ) : (Model.mk op s1 s2 so w).s1 j = s1 j := rfl
theorem s2_mk (j : ℕ) : (Model.mk op s1 s2 so w).s2 j = s2 j := rfl
theorem so_mk : (Model.mk op s1 s2 so w).so = so := rfl
theorem w_mk (j r : ℕ) : (Model.mk op s1 s2 so w).w j r = w j r := rfl
end mklemmas

def Model.sv (n : ℕ) (M : Model) (j k r : ℕ) : Bool :=
  if k < n then r.testBit k else if k < n + j then M.w (k - n) r else false

def gfun (t : ℕ) (a b : Bool) : Bool :=
  if t = 0 then a && b else if t = 1 then a || b else true

def Valid (n s : ℕ) (g : ℕ → Bool) (R : ℕ → Prop) (M : Model) : Prop :=
  (∀ j < s, M.op j < 3) ∧ (∀ j < s, M.s1 j ≤ n + j) ∧ (∀ j < s, M.s2 j ≤ n + j) ∧
    M.so ≤ n + s ∧
    (∀ j < s, ∀ r, R r → M.w j r = gfun (M.op j) (M.sv n j (M.s1 j) r) (M.sv n j (M.s2 j) r)) ∧
    (∀ r, R r → M.sv n s M.so r = g r)

section validacc
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
include hv
theorem Valid.op_lt : ∀ j < s, M.op j < 3 := hv.1
theorem Valid.s1_le : ∀ j < s, M.s1 j ≤ n + j := hv.2.1
theorem Valid.s2_le : ∀ j < s, M.s2 j ≤ n + j := hv.2.2.1
theorem Valid.so_le : M.so ≤ n + s := hv.2.2.2.1
theorem Valid.w_eq : ∀ j < s, ∀ r, R r →
    M.w j r = gfun (M.op j) (M.sv n j (M.s1 j) r) (M.sv n j (M.s2 j) r) := hv.2.2.2.2.1
theorem Valid.out_eq : ∀ r, R r → M.sv n s M.so r = g r := hv.2.2.2.2.2
end validacc

abbrev Model.pad (n : ℕ) (M : Model) (j : ℕ) : Prop :=
  M.op j = 2 ∧ M.s1 j = n + j ∧ M.s2 j = n + j

def NF (n s : ℕ) (M : Model) : Prop :=
  (∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j) ∧
    (∀ j < s, M.op j = 2 → M.pad n j) ∧
    (∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j) ∧
    (∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i) ∧
    (∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j) ∧
    (∀ j, j + 1 < s → ¬ M.pad n j → ∃ i, j < i ∧ i < s ∧ (M.s1 i = n + j ∨ M.s2 i = n + j)) ∧
    (0 < s → M.so = n + s - 1 ∨ M.pad n (s - 1))

section nfacc
variable {n s : ℕ} {M : Model} (hn : NF n s M)
include hn
theorem NF.pre : ∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j := hn.1
theorem NF.padOp : ∀ j < s, M.op j = 2 → M.pad n j := hn.2.1
theorem NF.noF : ∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j := hn.2.2.1
theorem NF.noPadRd : ∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i := hn.2.2.2.1
theorem NF.ord : ∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j := hn.2.2.2.2.1
theorem NF.used : ∀ j, j + 1 < s → ¬ M.pad n j →
    ∃ i, j < i ∧ i < s ∧ (M.s1 i = n + j ∨ M.s2 i = n + j) := hn.2.2.2.2.2.1
theorem NF.out : 0 < s → M.so = n + s - 1 ∨ M.pad n (s - 1) := hn.2.2.2.2.2.2
end nfacc

section formula
variable (n s : ℕ)

def wd : ℕ := 2 ^ n + n + s + 1

def ix (kd j a : ℕ) : ℕ := (kd * (s + 1) + j) * wd n s + a

def P (v : ℕ) : ℕ := 2 * v + 2

def Q (v : ℕ) : ℕ := 2 * v + 3

def L (v : ℕ) (b : Bool) : ℕ := if b then P v else Q v

def pairs (m : ℕ) : List (ℕ × ℕ) :=
  (List.range m).flatMap fun b => (List.range b).map fun a => (a, b)

def fOp : List (List ℕ) :=
  (List.range s).map fun j => [P (ix n s 0 j 0), P (ix n s 0 j 1), P (ix n s 0 j 2)]

def fSrcAlo : List (List ℕ) :=
  [1, 2].flatMap fun e => (List.range s).map fun j =>
    (List.range (n + j + 1)).map fun k => P (ix n s e j k)

def srcEq (e j k r : ℕ) : List (List ℕ) :=
  if k < n then [[Q (ix n s e j k), L (ix n s (e + 3) j r) (r.testBit k)]]
  else if k < n + j then
    [[Q (ix n s e j k), Q (ix n s (e + 3) j r), P (ix n s 3 (k - n) r)],
     [Q (ix n s e j k), P (ix n s (e + 3) j r), Q (ix n s 3 (k - n) r)]]
  else [[Q (ix n s e j k), Q (ix n s (e + 3) j r)]]

def fSrcEq (rows : List ℕ) : List (List ℕ) :=
  [1, 2].flatMap fun e => (List.range s).flatMap fun j => rows.flatMap fun r =>
    (List.range (n + j + 1)).flatMap fun k => srcEq n s e j k r

def gateCl (j r : ℕ) : List (List ℕ) :=
  [[Q (ix n s 0 j 0), Q (ix n s 3 j r), P (ix n s 4 j r)],
   [Q (ix n s 0 j 0), Q (ix n s 3 j r), P (ix n s 5 j r)],
   [Q (ix n s 0 j 0), P (ix n s 3 j r), Q (ix n s 4 j r), Q (ix n s 5 j r)],
   [Q (ix n s 0 j 1), P (ix n s 3 j r), Q (ix n s 4 j r)],
   [Q (ix n s 0 j 1), P (ix n s 3 j r), Q (ix n s 5 j r)],
   [Q (ix n s 0 j 1), Q (ix n s 3 j r), P (ix n s 4 j r), P (ix n s 5 j r)],
   [Q (ix n s 0 j 2), P (ix n s 3 j r)]]

def fGate (rows : List ℕ) : List (List ℕ) :=
  (List.range s).flatMap fun j => rows.flatMap fun r => gateCl n s j r

def fOutAlo : List (List ℕ) := [(List.range (n + s + 1)).map fun k => P (ix n s 6 0 k)]

def outEq (g : ℕ → Bool) (k r : ℕ) : List (List ℕ) :=
  if k < n then (if r.testBit k = g r then [] else [[Q (ix n s 6 0 k)]])
  else if k < n + s then [[Q (ix n s 6 0 k), L (ix n s 3 (k - n) r) (g r)]]
  else if g r = true then [[Q (ix n s 6 0 k)]] else []

def fOutEq (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) :=
  rows.flatMap fun r => (List.range (n + s + 1)).flatMap fun k => outEq n s g k r

def fOut : List (List ℕ) :=
  if s = 0 then [] else [[P (ix n s 6 0 (n + s - 1)), P (ix n s 7 (s - 1) 0)]]

def fPad : List (List ℕ) :=
  (List.range s).flatMap fun j =>
    [[Q (ix n s 7 j 0), P (ix n s 0 j 2)], [Q (ix n s 7 j 0), P (ix n s 1 j (n + j))],
     [Q (ix n s 7 j 0), P (ix n s 2 j (n + j))], [P (ix n s 7 j 0), Q (ix n s 0 j 2)],
     [P (ix n s 7 j 0), Q (ix n s 1 j (n + j))], [P (ix n s 7 j 0), Q (ix n s 2 j (n + j))]]

def fPre : List (List ℕ) :=
  (List.range (s - 1)).map fun j => [Q (ix n s 7 (j + 1) 0), P (ix n s 7 j 0)]

def fPadRd : List (List ℕ) :=
  (List.range s).flatMap fun j => (List.range j).flatMap fun i =>
    [[Q (ix n s 7 i 0), Q (ix n s 1 j (n + i))], [Q (ix n s 7 i 0), Q (ix n s 2 j (n + i))]]

def fOrd : List (List ℕ) :=
  (List.range s).flatMap fun j => (List.range (n + j + 1)).flatMap fun k =>
    (List.range (k + 1)).map fun l => [Q (ix n s 1 j k), Q (ix n s 2 j l), P (ix n s 7 j 0)]

def fUsed : List (List ℕ) :=
  (List.range (s - 1)).map fun j =>
    ((List.range (s - 1 - j)).map fun t => P (ix n s 1 (j + 1 + t) (n + j))) ++
    ((List.range (s - 1 - j)).map fun t => P (ix n s 2 (j + 1 + t) (n + j))) ++
      [P (ix n s 7 j 0)]

def enc (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) :=
  fOp n s ++ fSrcAlo n s ++ fSrcEq n s rows ++ fGate n s rows ++ fOutAlo n s ++
    fOutEq n s g rows ++ fOut n s ++ fPad n s ++ fPre n s ++ fPadRd n s ++ fOrd n s ++
    fUsed n s

end formula

def rowFun (n : ℕ) (f : (Fin n → Bool) → Bool) (r : ℕ) : Bool := f fun i => r.testBit i

def meaning (n : ℕ) (M : Model) (kd j a : ℕ) : Bool :=
  if kd = 0 then M.op j == a else if kd = 1 then M.s1 j == a else if kd = 2 then M.s2 j == a
  else if kd = 3 then M.w j a else if kd = 4 then M.sv n j (M.s1 j) a
  else if kd = 5 then M.sv n j (M.s2 j) a else if kd = 6 then M.so == a
  else if kd = 7 then decide (M.pad n j) else false

def val (n s : ℕ) (M : Model) (x : ℕ) : Bool :=
  meaning n M ((x - 1) / wd n s / (s + 1)) ((x - 1) / wd n s % (s + 1)) ((x - 1) % wd n s)

theorem val_ix (n s : ℕ) (M : Model) {kd j a : ℕ} (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s kd j a + 1) = meaning n M kd j a := by
  have hw : 0 < wd n s := Nat.succ_pos _
  unfold val ix
  rw [Nat.add_sub_cancel]
  have h1 : ((kd * (s + 1) + j) * wd n s + a) / wd n s = kd * (s + 1) + j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt ha, Nat.zero_add]
  have h2 : ((kd * (s + 1) + j) * wd n s + a) % wd n s = a := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
  have h3 : (kd * (s + 1) + j) / (s + 1) = kd := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega),
      Nat.zero_add]
  have h4 : (kd * (s + 1) + j) % (s + 1) = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  rw [h1, h2, h3, h4]

theorem litVal_P (a : ℕ → Bool) (v : ℕ) : litVal a (P v) = a (v + 1) := by
  unfold litVal P
  rw [show (2 * v + 2) / 2 = v + 1 by omega, show (2 * v + 2) % 2 = 0 by omega]
  cases a (v + 1) <;> rfl

theorem litVal_Q (a : ℕ → Bool) (v : ℕ) : litVal a (Q v) = !a (v + 1) := by
  unfold litVal Q
  rw [show (2 * v + 3) / 2 = v + 1 by omega, show (2 * v + 3) % 2 = 1 by omega]
  cases a (v + 1) <;> rfl

theorem litVal_L (a : ℕ → Bool) (v : ℕ) (b : Bool) : litVal a (L v b) = (a (v + 1) == b) := by
  cases b <;> simp [L, litVal_P, litVal_Q]

theorem cs_cons (a : ℕ → Bool) (l : ℕ) (c : List ℕ) :
    ClauseSat a (l :: c) ↔ litVal a l = true ∨ ClauseSat a c := by
  simp [ClauseSat]

theorem cs_nil (a : ℕ → Bool) : ClauseSat a [] ↔ False := by simp [ClauseSat]

theorem cs_of_mem {a : ℕ → Bool} {c : List ℕ} {l : ℕ} (h : l ∈ c) (hl : litVal a l = true) :
    ClauseSat a c := ⟨l, h, hl⟩

section vlemmas
variable {n s : ℕ} (M : Model) {j a : ℕ}

theorem wd_lt1 (h : a ≤ n + s + 1) : a < wd n s := by
  have := Nat.one_le_two_pow (n := n); unfold wd; omega
theorem wd_lt2 (h : a < 2 ^ n) : a < wd n s := by unfold wd; omega

theorem v_op (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 0 j a + 1) = (M.op j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_s1 (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 1 j a + 1) = (M.s1 j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_s2 (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 2 j a + 1) = (M.s2 j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_w (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 3 j a + 1) = M.w j a := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_u1 (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s 4 j a + 1) = M.sv n j (M.s1 j) a := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_u2 (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s 5 j a + 1) = M.sv n j (M.s2 j) a := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_so (ha : a < wd n s) : val n s M (ix n s 6 0 a + 1) = (M.so == a) := by
  rw [val_ix n s M (Nat.zero_le _) ha]; simp [meaning]
theorem v_pad (hj : j ≤ s) : val n s M (ix n s 7 j 0 + 1) = decide (M.pad n j) := by
  rw [val_ix n s M hj (wd_lt1 (by omega))]; simp [meaning]

end vlemmas

def Model.src (M : Model) (e j : ℕ) : ℕ := if e = 1 then M.s1 j else M.s2 j

theorem v_src {n s : ℕ} (M : Model) {e j a : ℕ} (he : e = 1 ∨ e = 2) (hj : j ≤ s)
    (ha : a < wd n s) : val n s M (ix n s e j a + 1) = (M.src e j == a) := by
  rcases he with rfl | rfl
  · exact v_s1 M hj ha
  · exact v_s2 M hj ha

theorem v_u {n s : ℕ} (M : Model) {e j a : ℕ} (he : e = 1 ∨ e = 2) (hj : j ≤ s)
    (ha : a < wd n s) : val n s M (ix n s (e + 3) j a + 1) = M.sv n j (M.src e j) a := by
  rcases he with rfl | rfl
  · exact v_u1 M hj ha
  · exact v_u2 M hj ha

section sound
variable {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {M : Model}
  (hrows : ∀ r ∈ rows, r < 2 ^ n) (hv : Valid n s g (· ∈ rows) M) (hn : NF n s M)
include hv

theorem src_le {e j : ℕ} (he : e = 1 ∨ e = 2) (hj : j < s) : M.src e j ≤ n + j := by
  rcases he with rfl | rfl
  · simpa [Model.src] using hv.s1_le j hj
  · simpa [Model.src] using hv.s2_le j hj

theorem s_fOp : ∀ c ∈ fOp n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOp, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  have := hv.op_lt j hj
  simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_P, v_op, beq_iff_eq, or_false]
  omega

theorem s_fSrcAlo : ∀ c ∈ fSrcAlo n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fSrcAlo, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  obtain ⟨e, he, j, hj, rfl⟩ := hc
  have hle := src_le hv he hj
  apply cs_of_mem (List.mem_map.2 ⟨M.src e j, List.mem_range.2 (by omega), rfl⟩)
  rw [litVal_P, v_src M he (by omega) (wd_lt1 (by omega))]
  simp

include hrows in
theorem s_fSrcEq : ∀ c ∈ fSrcEq n s rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fSrcEq, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨e, he, j, hj, r, hr, k, hk, hc⟩ := hc
  have hr' := hrows r hr
  unfold srcEq at hc
  split_ifs at hc with h1 h2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_L, v_src M he, v_u M he,
      or_false]
    by_cases hs : M.src e j = k
    · right; rw [hs]; simp [Model.sv, h1]
    · left; simp [hs]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
    · simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_src M he, v_u M he, v_w,
        or_false]
      by_cases hs : M.src e j = k
      · rw [hs]
        have : M.sv n j k r = M.w (k - n) r := by simp [Model.sv, h1, h2]
        rw [this]
        cases M.w (k - n) r <;> simp
      · simp [hs]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, v_src M he, v_u M he, or_false]
    by_cases hs : M.src e j = k
    · right; rw [hs]; simp [Model.sv, h1, h2]
    · left; simp [hs]

omit hv in
theorem gate_fact (t : ℕ) (ht : t < 3) (x a b : Bool) (hw : x = gfun t a b) :
    ((!(t == 0) || !x || a) = true) ∧ ((!(t == 0) || !x || b) = true) ∧
    ((!(t == 0) || x || !a || !b) = true) ∧ ((!(t == 1) || x || !a) = true) ∧
    ((!(t == 1) || x || !b) = true) ∧ ((!(t == 1) || !x || a || b) = true) ∧
    ((!(t == 2) || x) = true) := by
  interval_cases t <;> cases x <;> cases a <;> cases b <;> simp_all [gfun]

include hrows in
theorem s_fGate : ∀ c ∈ fGate n s rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fGate, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨j, hj, r, hr, hc⟩ := hc
  have hr' := hrows r hr
  have G := gate_fact _ (hv.op_lt j hj) _ _ _ (hv.w_eq j hj r hr)
  simp only [gateCl, List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain ⟨G1, G2, G3, G4, G5, G6, G7⟩ := G
  simp only [Bool.or_eq_true, or_assoc] at G1 G2 G3 G4 G5 G6 G7
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_op, v_w, v_u1, v_u2,
      or_false, or_assoc] <;> assumption

theorem s_fOutAlo : ∀ c ∈ fOutAlo n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOutAlo, List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc
  have := hv.so_le
  apply cs_of_mem (List.mem_map.2 ⟨M.so, List.mem_range.2 (by omega), rfl⟩)
  rw [litVal_P, v_so M (wd_lt1 (by omega))]
  simp

include hrows in
theorem s_fOutEq : ∀ c ∈ fOutEq n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOutEq, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨r, hr, k, hk, hc⟩ := hc
  have hr' := hrows r hr
  have ho := hv.out_eq r hr
  unfold outEq at hc
  by_cases h1 : k < n
  · rw [if_pos h1] at hc
    by_cases h2 : r.testBit k = g r
    · rw [if_pos h2] at hc; simp at hc
    · rw [if_neg h2] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, v_so, or_false]
      by_cases e : M.so = k
      · rw [e] at ho
        simp only [Model.sv, if_pos h1] at ho
        exact absurd ho h2
      · simp [e]
  · rw [if_neg h1] at hc
    by_cases h3 : k < n + s
    · rw [if_pos h3] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_L, v_so, v_w, or_false]
      by_cases e : M.so = k
      · rw [e] at ho
        simp only [Model.sv, if_neg h1, if_pos h3] at ho
        right; rw [ho]; simp
      · simp [e]
    · rw [if_neg h3] at hc
      by_cases h4 : g r = true
      · rw [if_pos h4] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        subst hc
        simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, v_so, or_false]
        by_cases e : M.so = k
        · rw [e] at ho
          simp only [Model.sv, if_neg h1, if_neg h3] at ho
          rw [h4] at ho
          exact absurd ho Bool.false_ne_true
        · simp [e]
      · rw [if_neg h4] at hc; simp at hc

include hn

theorem s_fOut : ∀ c ∈ fOut n s, ClauseSat (val n s M) c := by
  intro c hc
  unfold fOut at hc
  split_ifs at hc with hs
  · simp at hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_P, v_so, v_pad, or_false, beq_iff_eq,
      decide_eq_true_eq]
    exact hn.out (by omega)

theorem s_fPad : ∀ c ∈ fPad n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPad, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨j, hj, hc⟩ := hc
  have h1 := hn.padOp j hj
  have h2 := hn.noF j hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_op, v_s1, v_s2, v_pad,
      or_false, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
      beq_eq_false_iff_ne, ne_eq]
    unfold Model.pad at *
    tauto

theorem s_fPre : ∀ c ∈ fPre n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPre, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_pad, or_false,
    decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  by_cases h : M.pad n (j + 1)
  · exact Or.inr (hn.pre j (by omega) h)
  · exact Or.inl h

theorem s_fPadRd : ∀ c ∈ fPadRd n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPadRd, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨j, hj, i, hi, hc⟩ := hc
  have h1 := hn.noPadRd j hj i hi
  rcases hc with rfl | rfl <;>
  · simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, v_s1, v_s2, v_pad, or_false,
      Bool.not_eq_true', decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq]
    tauto

theorem s_fOrd : ∀ c ∈ fOrd n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOrd, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, k, hk, l, hl, rfl⟩ := hc
  simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_s1, v_s2, v_pad, or_false,
    Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, decide_eq_true_eq]
  by_cases hp : M.pad n j
  · exact Or.inr (Or.inr hp)
  · have := hn.ord j hj hp
    omega

theorem s_fUsed : ∀ c ∈ fUsed n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fUsed, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  by_cases hp : M.pad n j
  · apply cs_of_mem (l := P (ix n s 7 j 0)) (by simp)
    rw [litVal_P, v_pad M (by omega)]
    simpa using hp
  · obtain ⟨i, hji, hi, h | h⟩ := hn.used j (by omega) hp
    · apply cs_of_mem (l := P (ix n s 1 (j + 1 + (i - j - 1)) (n + j)))
      · apply List.mem_append_left; apply List.mem_append_left
        exact List.mem_map.2 ⟨i - j - 1, List.mem_range.2 (by omega), rfl⟩
      · rw [litVal_P, v_s1 M (by omega) (wd_lt1 (by omega)),
          show j + 1 + (i - j - 1) = i by omega]
        simpa using h
    · apply cs_of_mem (l := P (ix n s 2 (j + 1 + (i - j - 1)) (n + j)))
      · apply List.mem_append_left; apply List.mem_append_right
        exact List.mem_map.2 ⟨i - j - 1, List.mem_range.2 (by omega), rfl⟩
      · rw [litVal_P, v_s2 M (by omega) (wd_lt1 (by omega)),
          show j + 1 + (i - j - 1) = i by omega]
        simpa using h

include hrows in

theorem enc_sat : ∀ c ∈ enc n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [enc, List.append_assoc, List.mem_append] at hc
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h
  · exact s_fOp hv c h
  · exact s_fSrcAlo hv c h
  · exact s_fSrcEq hrows hv c h
  · exact s_fGate hrows hv c h
  · exact s_fOutAlo hv c h
  · exact s_fOutEq hrows hv c h
  · exact s_fOut hv hn c h
  · exact s_fPad hv hn c h
  · exact s_fPre hv hn c h
  · exact s_fPadRd hv hn c h
  · exact s_fOrd hv hn c h
  · exact s_fUsed hv hn c h

end sound

section circuit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def xr (n r : ℕ) : List Bool := List.ofFn fun i : Fin n => r.testBit i

def nm (n j a : ℕ) : ℕ := if a < n + j then a else n + j

def code (n : ℕ) (g : Gate) (j : ℕ) : ℕ × ℕ × ℕ :=
  match g.op, g.inputs with
  | .and, [] => (2, n + j, n + j)
  | .and, [a] => (0, nm n j a, nm n j a)
  | .and, a :: b :: _ => (0, nm n j a, nm n j b)
  | .or, [] => (1, n + j, n + j)
  | .or, [a] => (1, nm n j a, nm n j a)
  | .or, a :: b :: _ => (1, nm n j a, nm n j b)
  | _, _ => (2, n + j, n + j)

def gateAt (C : Circuit) (j : ℕ) : Gate := C.gates.getD j ⟨.and, []⟩

def ofCirc (n s : ℕ) (C : Circuit) : Model :=
  Model.mk (fun j => (code n (gateAt C j) j).1) (fun j => (code n (gateAt C j) j).2.1)
    (fun j => (code n (gateAt C j) j).2.2)
    (if C.output < n + C.gates.length then C.output else n + s)
    (fun j r => if j < C.gates.length then (C.wires (xr n r)).getD (n + j) false else true)

theorem xr_length (n r : ℕ) : (xr n r).length = n := by simp [xr]

theorem xr_getD (n r a : ℕ) (ha : a < n) : (xr n r).getD a false = r.testBit a := by
  simp [xr, List.getD_eq_getElem?_getD, ha]

theorem code_le (n : ℕ) (g : Gate) (j : ℕ) :
    (code n g j).1 < 3 ∧ (code n g j).2.1 ≤ n + j ∧ (code n g j).2.2 ≤ n + j := by
  have h : ∀ a, nm n j a ≤ n + j := fun a => by unfold nm; split_ifs <;> omega
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp [code, h]

theorem code_eval (n : ℕ) (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (j : ℕ) (S : ℕ → Bool) (hS : S (n + j) = false) :
    g.op.eval (g.inputs.map fun i => S (nm n j i)) =
      gfun (code n g j).1 (S (code n g j).2.1) (S (code n g j).2.2) := by
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  dsimp only at hlen
  rcases hop with rfl | rfl <;>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    simp_all [code, GateOp.eval, gfun]

theorem wire_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        (wiresFrom (C.gates.take j) x).getD i false) ∧
    ∀ i, (wiresFrom (C.gates.take j) x).getD i false =
      if i < x.length + j then (C.wires x).getD i false else false := by
  have hsplit : C.gates = C.gates.take j ++ (gateAt C j :: C.gates.drop (j + 1)) := by
    rw [gateAt, List.getD_eq_getElem _ _ hj, List.cons_getElem_drop_succ, List.take_append_drop]
  set V := wiresFrom (C.gates.take j) x with hV
  have hVl : V.length = x.length + j := by
    rw [hV, length_wiresFrom, List.length_take]; omega
  set e := (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => V.getD i false)
  have hw : C.wires x = wiresFrom (C.gates.drop (j + 1)) (V ++ [e]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append]; rfl
  have hpre : ∀ i < x.length + j + 1, (C.wires x).getD i false = (V ++ [e]).getD i false := by
    intro i hi
    rw [hw, getD_wiresFrom _ _ _ (by simp [hVl]; omega)]
  refine ⟨?_, ?_⟩
  · rw [hpre _ (by omega), ← hVl, getD_snoc_eq]
  · intro i
    split_ifs with hi
    · rw [hpre i (by omega), List.getD_append _ _ _ _ (by omega)]
    · exact List.getD_eq_default _ _ (by omega)
  where
    getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by simp

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  rw [wires_eq, length_wiresFrom]

theorem ofCirc_sv (n s : ℕ) (C : Circuit) (j r k : ℕ) (hj : k < n + C.gates.length)
    (hk : k < n + j) : (ofCirc n s C).sv n j k r = (C.wires (xr n r)).getD k false := by
  unfold Model.sv
  by_cases h6 : k < n
  · rw [if_pos h6, wires_eq, getD_wiresFrom _ _ _ (by rw [xr_length]; exact h6),
      xr_getD n r k h6]
  · rw [if_neg h6, if_pos hk]
    simp only [ofCirc, show k - n < C.gates.length by omega, if_true, op_mk, s1_mk, s2_mk, so_mk, w_mk]
    congr 1
    omega

theorem valid_ofCirc (n s : ℕ) (g : ℕ → Bool) (R : ℕ → Prop) (C : Circuit) (hC : Monotone2 C)
    (hsz : C.gates.length ≤ s) (hev : ∀ r, R r → C.eval (xr n r) = g r) :
    Valid n s g R (ofCirc n s C) := by
  refine ⟨fun j _ => (code_le n _ j).1, fun j _ => (code_le n _ j).2.1,
    fun j _ => (code_le n _ j).2.2, ?_, ?_, ?_⟩
  · simp only [ofCirc, op_mk, s1_mk, s2_mk, so_mk, w_mk]; split_ifs <;> omega
  · intro j hj r _
    by_cases hjl : j < C.gates.length
    · have hmem : gateAt C j ∈ C.gates := by
        rw [gateAt, List.getD_eq_getElem _ _ hjl]; exact List.getElem_mem hjl
      have hg := hC (gateAt C j) hmem
      obtain ⟨h1, h2⟩ := wire_gate C (xr n r) j hjl
      rw [xr_length] at h1 h2
      have hS : ∀ i, (wiresFrom (C.gates.take j) (xr n r)).getD i false =
          (ofCirc n s C).sv n j (nm n j i) r := by
        intro i
        rw [h2 i]
        unfold nm
        split_ifs with hi
        · rw [ofCirc_sv n s C j r i (by omega) hi]
        · simp [Model.sv]
      simp only [hS] at h1
      have hw : (ofCirc n s C).w j r = if j < C.gates.length then
          (C.wires (xr n r)).getD (n + j) false else true := rfl
      rw [hw, if_pos hjl, h1, code_eval n _ hg.1 hg.2 j (fun k => (ofCirc n s C).sv n j k r)
        (by simp [Model.sv])]
      rfl
    · have hga : gateAt C j = ⟨.and, []⟩ := by
        rw [gateAt, List.getD_eq_default _ _ (by omega)]
      simp [ofCirc, hjl, hga, code, gfun, op_mk, s1_mk, s2_mk, so_mk, w_mk]
  · intro r hr
    rw [← hev r hr, Circuit.eval]
    have hso : (ofCirc n s C).so =
        if C.output < n + C.gates.length then C.output else n + s := rfl
    rw [hso]
    split_ifs with ho
    · by_cases h6 : C.output < n
      · simp only [Model.sv, if_pos h6]
        rw [wires_eq, getD_wiresFrom _ _ _ (by rw [xr_length]; exact h6), xr_getD n r _ h6]
      · rw [ofCirc_sv n s C s r _ ho (by omega)]
    · rw [List.getD_eq_default _ _ (by rw [wires_length, xr_length]; omega)]
      simp [Model.sv]

end circuit

def phi (n d k : ℕ) : ℕ := if k < n then k else if k < n + d then k + 1 else k

def rd (n d t j k : ℕ) : ℕ :=
  if k = n + d then (if t = 0 then n + j else if t = 1 then n else phi n d (t - 2)) else phi n d k

def tval (n : ℕ) (M : Model) (d t r : ℕ) : Bool :=
  if t = 0 then false else if t = 1 then true else M.sv n d (t - 2) r

def mv (n s : ℕ) (M : Model) (d t : ℕ) : Model :=
  Model.mk (fun j => if j = 0 then 2 else if j ≤ d then M.op (j - 1) else M.op j)
    (fun j => if j = 0 then n else if j ≤ d then phi n d (M.s1 (j - 1)) else rd n d t j (M.s1 j))
    (fun j => if j = 0 then n else if j ≤ d then phi n d (M.s2 (j - 1)) else rd n d t j (M.s2 j))
    (rd n d t s M.so)
    (fun j r => if j = 0 then true else if j ≤ d then M.w (j - 1) r else M.w j r)

def Model.Read (n s : ℕ) (M : Model) (d : ℕ) : Prop :=
  (∃ j, d < j ∧ j < s ∧ (M.s1 j = n + d ∨ M.s2 j = n + d)) ∨ M.so = n + d

def TgtOk (n d t : ℕ) : Prop := t = 0 ∨ t = 1 ∨ (2 ≤ t ∧ t - 2 < n + d)

section move
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}

theorem sv_shift (hd : d < s) {i k r : ℕ} (hi : i < d) (hk : k ≤ n + i) :
    (mv n s M d t).sv n (i + 1) (phi n d k) r = M.sv n i k r := by
  unfold Model.sv phi
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + i
    · simp only [if_neg h6, if_pos (show k < n + d by omega), if_neg (show ¬ k + 1 < n by omega),
        if_pos (show k + 1 < n + (i + 1) by omega), if_pos h7, mv,
        if_neg (show ¬ k + 1 - n = 0 by omega), if_pos (show k + 1 - n ≤ d by omega), op_mk, s1_mk, s2_mk, so_mk, w_mk]
      congr 1 <;> omega
    · simp only [if_neg h6, if_pos (show k < n + d by omega), if_neg (show ¬ k + 1 < n by omega),
        if_neg (show ¬ k + 1 < n + (i + 1) by omega), if_neg h7]

theorem sv_later {j k r : ℕ} (hj : d < j) (hkd : k ≠ n + d) :
    (mv n s M d t).sv n j (phi n d k) r = M.sv n j k r := by
  unfold Model.sv phi
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + d
    · simp only [if_neg h6, if_pos h7, if_neg (show ¬ k + 1 < n by omega),
        if_pos (show k + 1 < n + j by omega), if_pos (show k < n + j by omega), mv,
        if_neg (show ¬ k + 1 - n = 0 by omega), if_pos (show k + 1 - n ≤ d by omega), op_mk, s1_mk, s2_mk, so_mk, w_mk]
      congr 1 <;> omega
    · simp only [if_neg h6, if_neg h7]
      by_cases h8 : k < n + j
      · simp only [if_pos h8, mv, if_neg (show ¬ k - n = 0 by omega),
          if_neg (show ¬ k - n ≤ d by omega), op_mk, s1_mk, s2_mk, so_mk, w_mk]
      · simp only [if_neg h8]

theorem sv_rd (ht : TgtOk n d t) {j k r : ℕ} (hj : d < j)
    (htr : k = n + d → M.w d r = tval n M d t r) :
    (mv n s M d t).sv n j (rd n d t j k) r = M.sv n j k r := by
  unfold rd
  by_cases hkd : k = n + d
  · rw [if_pos hkd]
    have hw := htr hkd
    have hold : M.sv n j k r = M.w d r := by
      unfold Model.sv
      simp only [if_neg (show ¬ k < n by omega), if_pos (show k < n + j by omega)]
      congr 1; omega
    rw [hold, hw]
    unfold tval
    rcases ht with rfl | rfl | ⟨h2, hc⟩
    · simp [Model.sv]
    · simp [Model.sv, mv, show 0 < j by omega, op_mk, s1_mk, s2_mk, so_mk, w_mk]
    · simp only [if_neg (show ¬ t = 0 by omega), if_neg (show ¬ t = 1 by omega)]
      rw [sv_later hj (by omega)]
      unfold Model.sv
      by_cases h6 : t - 2 < n
      · simp [h6]
      · simp only [if_neg h6, if_pos (show t - 2 < n + j by omega), if_pos hc]
  · rw [if_neg hkd]
    exact sv_later hj hkd

theorem valid_mv (hv : Valid n s g R M) (hd : d < s) (ht : TgtOk n d t)
    (htr : M.Read n s d → ∀ r, R r → M.w d r = tval n M d t r) :
    Valid n s g R (mv n s M d t) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    simp only [mv, op_mk, s1_mk, s2_mk, so_mk, w_mk]; split_ifs
    · omega
    · exact hv.op_lt _ (by omega)
    · exact hv.op_lt _ hj
  · intro j hj
    simp only [mv, op_mk, s1_mk, s2_mk, so_mk, w_mk]; split_ifs with h0 h1
    · omega
    · have := hv.s1_le (j - 1) (by omega); unfold phi; split_ifs <;> omega
    · have := hv.s1_le j hj
      unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  · intro j hj
    simp only [mv, op_mk, s1_mk, s2_mk, so_mk, w_mk]; split_ifs with h0 h1
    · omega
    · have := hv.s2_le (j - 1) (by omega); unfold phi; split_ifs <;> omega
    · have := hv.s2_le j hj
      unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  · have := hv.so_le
    simp only [mv, op_mk, s1_mk, s2_mk, so_mk, w_mk]; unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  · intro j hj r hr
    by_cases h0 : j = 0
    · subst h0; simp [mv, gfun, op_mk, s1_mk, s2_mk, so_mk, w_mk]
    · by_cases h1 : j ≤ d
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have e1 := sv_shift (M := M) (t := t) hd (i := i) (r := r) (by omega)
          (hv.s1_le i (by omega))
        have e2 := sv_shift (M := M) (t := t) hd (i := i) (r := r) (by omega)
          (hv.s2_le i (by omega))
        simp only [mv, if_neg h0, if_pos h1, Nat.add_sub_cancel, op_mk, s1_mk, s2_mk, so_mk, w_mk] at e1 e2 ⊢
        rw [e1, e2]
        exact hv.w_eq i (by omega) r hr
      · have e1 := sv_rd (s := s) (M := M) ht (j := j) (k := M.s1 j) (r := r) (by omega)
          (fun h => htr (Or.inl ⟨j, by omega, hj, Or.inl h⟩) r hr)
        have e2 := sv_rd (s := s) (M := M) ht (j := j) (k := M.s2 j) (r := r) (by omega)
          (fun h => htr (Or.inl ⟨j, by omega, hj, Or.inr h⟩) r hr)
        simp only [mv, if_neg h0, if_neg h1, op_mk, s1_mk, s2_mk, so_mk, w_mk] at e1 e2 ⊢
        rw [e1, e2]
        exact hv.w_eq j hj r hr
  · intro r hr
    have e := sv_rd (s := s) (M := M) ht (j := s) (k := M.so) (r := r) hd
      (fun h => htr (Or.inr h) r hr)
    simp only [mv, op_mk, s1_mk, s2_mk, so_mk, w_mk] at e ⊢
    rw [e]
    exact hv.out_eq r hr

theorem pad_mv0 : (mv n s M d t).pad n 0 := by simp [Model.pad, mv, op_mk, s1_mk, s2_mk, so_mk, w_mk]

theorem pad_mv_shift (hv : Valid n s g R M) {i : ℕ} (hi : i < d) (hd : d < s) :
    (mv n s M d t).pad n (i + 1) ↔ M.pad n i := by
  have h1 := hv.s1_le i (by omega)
  have h2 := hv.s2_le i (by omega)
  simp only [Model.pad, mv, if_neg (show ¬ i + 1 = 0 by omega), if_pos (show i + 1 ≤ d by omega),
    Nat.add_sub_cancel, op_mk, s1_mk, s2_mk, so_mk, w_mk]
  unfold phi
  constructor
  · rintro ⟨a, b, c⟩; refine ⟨a, ?_, ?_⟩ <;> split_ifs at b c <;> omega
  · rintro ⟨a, b, c⟩; refine ⟨a, ?_, ?_⟩ <;> split_ifs <;> omega

theorem pad_mv_later {j : ℕ} (hj : d < j) (h : M.pad n j) : (mv n s M d t).pad n j := by
  obtain ⟨a, b, c⟩ := h
  simp only [Model.pad, mv, if_neg (show ¬ j = 0 by omega), if_neg (show ¬ j ≤ d by omega), op_mk, s1_mk, s2_mk, so_mk, w_mk]
  refine ⟨a, ?_, ?_⟩ <;> unfold rd phi <;> split_ifs <;> omega

end move

def ind (n : ℕ) (M : Model) (j : ℕ) : ℕ := if M.pad n j then 0 else 1

def muf (s : ℕ) (a : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range s, (s - j) * a j

theorem muf_lt (s : ℕ) (a b : ℕ → ℕ) (d : ℕ) (hd : d < s) (hb0 : b 0 = 0)
    (hsh : ∀ i < d, b (i + 1) = a i) (hle : ∀ j, d < j → j < s → b j ≤ a j)
    (hpos : 0 < a d ∨ ∃ i < d, 0 < a i) : muf s b < muf s a := by
  have base : ∑ j ∈ Finset.range (d + 1), (s - j) * b j <
      ∑ j ∈ Finset.range (d + 1), (s - j) * a j := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ, hb0, Nat.mul_zero, Nat.add_zero]
    have e1 : ∑ i ∈ Finset.range d, (s - (i + 1)) * b (i + 1) =
        ∑ i ∈ Finset.range d, (s - (i + 1)) * a i :=
      Finset.sum_congr rfl fun i hi => by rw [hsh i (Finset.mem_range.1 hi)]
    have e2 : ∑ i ∈ Finset.range d, (s - i) * a i =
        ∑ i ∈ Finset.range d, (s - (i + 1)) * a i + ∑ i ∈ Finset.range d, a i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have := Finset.mem_range.1 hi
      rw [show s - i = (s - (i + 1)) + 1 by omega, Nat.add_mul, Nat.one_mul]
    rw [e1, e2]
    have : 0 < ∑ i ∈ Finset.range d, a i + (s - d) * a d := by
      rcases hpos with h | ⟨i, hi, h⟩
      · have : 0 < (s - d) * a d := Nat.mul_pos (by omega) h
        omega
      · have := Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.2 hi)
        omega
    omega
  have step : ∀ m, d + 1 ≤ m → m ≤ s → ∑ j ∈ Finset.range m, (s - j) * b j <
      ∑ j ∈ Finset.range m, (s - j) * a j := by
    intro m hm hms
    induction m with
    | zero => omega
    | succ m ih =>
      by_cases h : m + 1 = d + 1
      · rw [h]; exact base
      · rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have := ih (by omega) (by omega)
        have : (s - m) * b m ≤ (s - m) * a m :=
          Nat.mul_le_mul_left _ (hle m (by omega) (by omega))
        omega
  exact step s (by omega) le_rfl

def sw (M : Model) (j : ℕ) : Model :=
  Model.mk M.op (fun i => if i = j then M.s2 j else M.s1 i)
    (fun i => if i = j then M.s1 j else M.s2 i) M.so M.w

theorem valid_sw {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (j : ℕ) : Valid n s g R (sw M j) := by
  refine ⟨hv.op_lt, ?_, ?_, hv.so_le, ?_, fun r hr => hv.out_eq r hr⟩
  · intro i hi
    simp only [sw, op_mk, s1_mk, s2_mk, so_mk, w_mk]; split_ifs with h
    · subst h; exact hv.s2_le i hi
    · exact hv.s1_le i hi
  · intro i hi
    simp only [sw, op_mk, s1_mk, s2_mk, so_mk, w_mk]; split_ifs with h
    · subst h; exact hv.s1_le i hi
    · exact hv.s2_le i hi
  · intro i hi r hr
    have := hv.w_eq i hi r hr
    have hsv : ∀ k, (sw M j).sv n i k r = M.sv n i k r := fun k => rfl
    simp only [hsv]
    simp only [sw, op_mk, s1_mk, s2_mk, so_mk, w_mk]
    split_ifs with h1
    · subst h1
      rw [this]; unfold gfun
      split_ifs <;> simp [Bool.and_comm, Bool.or_comm]
    · exact this

theorem pad_sw {n : ℕ} {M : Model} {j : ℕ} (i : ℕ) : (sw M j).pad n i ↔ M.pad n i := by
  simp only [Model.pad, sw, op_mk, s1_mk, s2_mk, so_mk, w_mk]
  split_ifs with h
  · subst h; constructor <;> rintro ⟨a, b, c⟩ <;> exact ⟨a, c, b⟩
  · rfl

section triv
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M) {j : ℕ}
  (hj : j < s)
include hv hj

theorem copy_tgt {k : ℕ} (hk : k ≤ n + j) (hw : ∀ r, R r → M.w j r = M.sv n j k r) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  by_cases hk' : k < n + j
  · refine ⟨k + 2, Or.inr (Or.inr ⟨by omega, by omega⟩), fun r hr => ?_⟩
    rw [hw r hr]; simp [tval]
  · refine ⟨0, Or.inl rfl, fun r hr => ?_⟩
    rw [hw r hr]; simp [tval, Model.sv, show ¬ k < n by omega, hk']

omit hv hj in
theorem const_tgt (c : Bool) (hw : ∀ r, R r → M.w j r = c) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  cases c
  · exact ⟨0, Or.inl rfl, fun r hr => by rw [hw r hr]; simp [tval]⟩
  · exact ⟨1, Or.inr (Or.inl rfl), fun r hr => by rw [hw r hr]; simp [tval]⟩

theorem op2_triv (h2 : M.op j = 2) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r :=
  const_tgt true fun r hr => by rw [hv.w_eq j hj r hr, h2]; simp [gfun]

theorem false_src
    (h : (∀ r, R r → M.sv n j (M.s1 j) r = false) ∨ (∀ r, R r → M.sv n j (M.s2 j) r = false)) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have hop := hv.op_lt j hj
  have hw := hv.w_eq j hj
  by_cases h0 : M.op j = 0
  · refine const_tgt false fun r hr => ?_
    rw [hw r hr, h0]
    rcases h with h | h <;> simp [gfun, h r hr]
  · by_cases h1 : M.op j = 1
    · rcases h with h | h
      · exact copy_tgt hv hj (hv.s2_le j hj) fun r hr => by rw [hw r hr, h1]; simp [gfun, h r hr]
      · exact copy_tgt hv hj (hv.s1_le j hj) fun r hr => by rw [hw r hr, h1]; simp [gfun, h r hr]
    · exact op2_triv hv hj (by omega)

theorem true_src
    (h : (∀ r, R r → M.sv n j (M.s1 j) r = true) ∨ (∀ r, R r → M.sv n j (M.s2 j) r = true)) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have hop := hv.op_lt j hj
  have hw := hv.w_eq j hj
  by_cases h0 : M.op j = 0
  · rcases h with h | h
    · exact copy_tgt hv hj (hv.s2_le j hj) fun r hr => by rw [hw r hr, h0]; simp [gfun, h r hr]
    · exact copy_tgt hv hj (hv.s1_le j hj) fun r hr => by rw [hw r hr, h0]; simp [gfun, h r hr]
  · by_cases h1 : M.op j = 1
    · refine const_tgt true fun r hr => ?_
      rw [hw r hr, h1]
      rcases h with h | h <;> simp [gfun, h r hr]
    · exact op2_triv hv hj (by omega)

theorem same_src (he : M.s1 j = M.s2 j) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have := hv.op_lt j hj
  by_cases h2 : M.op j = 2
  · exact op2_triv hv hj h2
  refine copy_tgt hv hj (hv.s1_le j hj) fun r hr => ?_
  rw [hv.w_eq j hj r hr, ← he]
  unfold gfun
  split_ifs <;> first | omega | cases M.sv n j (M.s1 j) r <;> rfl

end triv

theorem pad_w {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    {i : ℕ} (hi : i < s) (hp : M.pad n i) {r : ℕ} (hr : R r) : M.w i r = true := by
  rw [hv.w_eq i hi r hr, hp.1]
  simp [gfun]

def lexWord (B : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => lexWord B a m * B + a m

theorem lexWord_lt {B : ℕ} {a : ℕ → ℕ} : ∀ m, (∀ i < m, a i < B) → lexWord B a m < B ^ m
  | 0, _ => by simp [lexWord]
  | m + 1, h => by
    have ih := lexWord_lt m (fun i hi => h i (by omega))
    have hm := h m (by omega)
    have h2 : (lexWord B a m + 1) * B ≤ B ^ m * B := Nat.mul_le_mul_right _ ih
    rw [Nat.add_mul, Nat.one_mul] at h2
    simp only [lexWord, pow_succ]
    omega

theorem lexWord_congr {B : ℕ} {a b : ℕ → ℕ} :
    ∀ m, (∀ i < m, a i = b i) → lexWord B a m = lexWord B b m
  | 0, _ => rfl
  | m + 1, h => by
    simp only [lexWord, lexWord_congr m (fun i hi => h i (by omega)), h m (by omega)]

theorem lexWord_lt_of {B : ℕ} {a b : ℕ → ℕ} {j : ℕ} (hab : ∀ i < j, a i = b i) (hj : b j < a j) :
    ∀ m, j < m → (∀ i < m, b i < B) → lexWord B b m < lexWord B a m
  | 0, h, _ => by omega
  | m + 1, hjm, hb => by
    by_cases h : m = j
    · subst h
      simp only [lexWord, lexWord_congr m hab]
      omega
    · have ih := lexWord_lt_of hab hj m (by omega) (fun i hi => hb i (by omega))
      have hm := hb m (by omega)
      have h2 : (lexWord B b m + 1) * B ≤ lexWord B a m * B := Nat.mul_le_mul_right _ ih
      rw [Nat.add_mul, Nat.one_mul] at h2
      simp only [lexWord]
      omega

def lexKey (n s : ℕ) (M : Model) (j : ℕ) : ℕ := M.s1 j * (3 * (n + s + 1)) + M.s2 j * 3 + M.op j

def lexB (n s : ℕ) : ℕ := 3 * (n + s + 1) * (n + s + 1)

theorem lex3 (K x1 y1 z1 x2 y2 z2 : ℕ) (hy : y1 * 3 + z1 < K) (hz : z1 < 3)
    (h : x1 < x2 ∨ (x1 = x2 ∧ (y1 < y2 ∨ (y1 = y2 ∧ z1 < z2)))) :
    x1 * K + y1 * 3 + z1 < x2 * K + y2 * 3 + z2 := by
  rcases h with h | ⟨rfl, h | ⟨rfl, h⟩⟩
  · have : (x1 + 1) * K ≤ x2 * K := Nat.mul_le_mul_right _ h
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  · omega
  · omega

section keys
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model}

theorem lexKey_lt (hv : Valid n s g R M) {j : ℕ} (hj : j < s) : lexKey n s M j < lexB n s := by
  have h1 := hv.s1_le j hj
  have h2 := hv.s2_le j hj
  have h3 := hv.op_lt j hj
  have : M.s1 j * (3 * (n + s + 1)) ≤ (n + s) * (3 * (n + s + 1)) :=
    Nat.mul_le_mul_right _ (by omega)
  have e : (n + s) * (3 * (n + s + 1)) + 3 * (n + s + 1) = 3 * (n + s + 1) * (n + s + 1) := by
    ring
  unfold lexKey lexB
  omega

def meas2 (n s : ℕ) (M : Model) : ℕ :=
  lexB n s ^ s * muf s (ind n M) + lexWord (lexB n s) (lexKey n s M) s

theorem lexWord_lt_pow (hv : Valid n s g R M) :
    lexWord (lexB n s) (lexKey n s M) s < lexB n s ^ s :=
  lexWord_lt s fun _ hi => lexKey_lt hv hi

end keys

theorem meas2_mv {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}
    (hv : Valid n s g R M) (hv' : Valid n s g R (mv n s M d t)) (hd : d < s)
    (hpos : ¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) : meas2 n s (mv n s M d t) < meas2 n s M := by
  have hlt : muf s (ind n (mv n s M d t)) < muf s (ind n M) := by
    apply muf_lt s (ind n M) (ind n (mv n s M d t)) d hd
    · simp [ind, pad_mv0]
    · intro i hi; simp only [ind, pad_mv_shift hv hi hd]
    · intro j hj _
      unfold ind
      by_cases h1 : (mv n s M d t).pad n j
      · rw [if_pos h1]; exact Nat.zero_le _
      · have h2 : ¬ M.pad n j := fun h => h1 (pad_mv_later hj h)
        simp [h1, h2]
    · rcases hpos with h | ⟨i, hi, h⟩
      · left; simp [ind, h]
      · right; exact ⟨i, hi, by simp [ind, h]⟩
  have b1 := lexWord_lt_pow hv'
  have : lexB n s ^ s * muf s (ind n (mv n s M d t)) + lexB n s ^ s ≤
      lexB n s ^ s * muf s (ind n M) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
  unfold meas2
  omega

theorem meas2_sw {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {j : ℕ}
    (hv : Valid n s g R M) (hj : j < s) (hlt : M.s2 j < M.s1 j) :
    meas2 n s (sw M j) < meas2 n s M := by
  have hind : ind n (sw M j) = ind n M := by funext i; simp [ind, pad_sw]
  unfold meas2
  rw [hind]
  have hk : lexKey n s (sw M j) j < lexKey n s M j := by
    have h1 := hv.s1_le j hj
    have : (M.s2 j + 1) * (3 * (n + s + 1)) ≤ M.s1 j * (3 * (n + s + 1)) :=
      Nat.mul_le_mul_right _ hlt
    rw [Nat.add_mul, Nat.one_mul] at this
    simp only [lexKey, sw, if_pos rfl, ↓reduceIte, op_mk, s1_mk, s2_mk, so_mk, w_mk]
    omega
  have := lexWord_lt_of (B := lexB n s) (a := lexKey n s M) (b := lexKey n s (sw M j)) (j := j)
    (fun i hi => by simp [lexKey, sw, show i ≠ j by omega, op_mk, s1_mk, s2_mk, so_mk, w_mk]) hk s hj
    (fun i hi => lexKey_lt (valid_sw hv j) hi)
  omega

def tsw (n j k : ℕ) : ℕ := if k = n + j then n + j + 1 else if k = n + j + 1 then n + j else k

def xsw (n : ℕ) (M : Model) (j : ℕ) : Model :=
  Model.mk (fun i => if i = j then M.op (j + 1) else if i = j + 1 then M.op j else M.op i)
    (fun i => if i = j then M.s1 (j + 1) else if i = j + 1 then M.s1 j
      else if j + 1 < i then tsw n j (M.s1 i) else M.s1 i)
    (fun i => if i = j then M.s2 (j + 1) else if i = j + 1 then M.s2 j
      else if j + 1 < i then tsw n j (M.s2 i) else M.s2 i)
    (tsw n j M.so)
    (fun i r => if i = j then M.w (j + 1) r else if i = j + 1 then M.w j r else M.w i r)

section xsw
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {j : ℕ}

theorem sv_xsw_low {i i' k r : ℕ} (hk : k < n + j) (hi : j ≤ i) (hi' : j ≤ i') :
    (xsw n M j).sv n i k r = M.sv n i' k r := by
  unfold Model.sv
  by_cases h6 : k < n
  · simp [h6]
  · simp only [if_neg h6, if_pos (show k < n + i by omega), if_pos (show k < n + i' by omega),
      xsw, if_neg (show k - n ≠ j by omega), if_neg (show k - n ≠ j + 1 by omega), op_mk, s1_mk, s2_mk, so_mk, w_mk]

theorem sv_xsw_early {i k r : ℕ} (hi : i < j) : (xsw n M j).sv n i k r = M.sv n i k r := by
  unfold Model.sv
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + i
    · simp only [if_neg h6, if_pos h7, xsw, if_neg (show k - n ≠ j by omega),
        if_neg (show k - n ≠ j + 1 by omega), op_mk, s1_mk, s2_mk, so_mk, w_mk]
    · simp only [if_neg h6, if_neg h7]

theorem sv_xsw_late {i k r : ℕ} (hi : j + 1 < i) :
    (xsw n M j).sv n i (tsw n j k) r = M.sv n i k r := by
  unfold tsw
  by_cases h1 : k = n + j
  · subst h1
    simp only [if_pos rfl, ↓reduceIte]
    unfold Model.sv
    simp only [if_neg (show ¬ n + j + 1 < n by omega), if_pos (show n + j + 1 < n + i by omega),
      if_neg (show ¬ n + j < n by omega), if_pos (show n + j < n + i by omega), xsw,
      show n + j + 1 - n = j + 1 by omega, show n + j - n = j by omega,
      if_neg (show j + 1 ≠ j by omega), if_pos rfl, ↓reduceIte, op_mk, s1_mk, s2_mk, so_mk, w_mk]
  · by_cases h2 : k = n + j + 1
    · subst h2
      simp only [if_neg h1, if_pos rfl, ↓reduceIte]
      unfold Model.sv
      simp only [if_neg (show ¬ n + j + 1 < n by omega), if_pos (show n + j + 1 < n + i by omega),
        if_neg (show ¬ n + j < n by omega), if_pos (show n + j < n + i by omega), xsw,
        show n + j + 1 - n = j + 1 by omega, show n + j - n = j by omega, if_pos rfl, ↓reduceIte, op_mk, s1_mk, s2_mk, so_mk, w_mk]
    · simp only [if_neg h1, if_neg h2]
      unfold Model.sv
      by_cases h6 : k < n
      · simp [h6]
      · by_cases h7 : k < n + i
        · simp only [if_neg h6, if_pos h7, xsw, if_neg (show k - n ≠ j by omega),
            if_neg (show k - n ≠ j + 1 by omega), op_mk, s1_mk, s2_mk, so_mk, w_mk]
        · simp only [if_neg h6, if_neg h7]

theorem tsw_le {i k : ℕ} (hi : j + 1 ≤ i) (hk : k ≤ n + i) : tsw n j k ≤ n + i := by
  unfold tsw; split_ifs <;> omega

theorem tsw_eq_iff {i k : ℕ} (hi : j + 1 < i) : tsw n j k = n + i ↔ k = n + i := by
  unfold tsw; split_ifs <;> omega

variable (hv : Valid n s g R M) (hj : j + 1 < s) (h1 : M.s1 j < n + j) (h2 : M.s2 j < n + j)
  (h3 : M.s1 (j + 1) < n + j) (h4 : M.s2 (j + 1) < n + j)
include hv hj h1 h2 h3 h4

theorem valid_xsw : Valid n s g R (xsw n M j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp only [xsw, op_mk, s1_mk, s2_mk, so_mk, w_mk]; split_ifs
    · exact hv.op_lt _ hj
    · exact hv.op_lt _ (by omega)
    · exact hv.op_lt _ hi
  · intro i hi
    simp only [xsw, op_mk, s1_mk, s2_mk, so_mk, w_mk]; split_ifs with a b c
    · omega
    · omega
    · exact tsw_le (by omega) (hv.s1_le i hi)
    · exact hv.s1_le i hi
  · intro i hi
    simp only [xsw, op_mk, s1_mk, s2_mk, so_mk, w_mk]; split_ifs with a b c
    · omega
    · omega
    · exact tsw_le (by omega) (hv.s2_le i hi)
    · exact hv.s2_le i hi
  · exact tsw_le (by omega) hv.so_le
  · intro i hi r hr
    by_cases a : i = j
    · subst a
      have e1 : (xsw n M i).s1 i = M.s1 (i + 1) := by simp [xsw, op_mk, s1_mk, s2_mk, so_mk, w_mk]
      have e2 : (xsw n M i).s2 i = M.s2 (i + 1) := by simp [xsw, op_mk, s1_mk, s2_mk, so_mk, w_mk]
      have e3 : (xsw n M i).op i = M.op (i + 1) := by simp [xsw, op_mk, s1_mk, s2_mk, so_mk, w_mk]
      have e4 : (xsw n M i).w i r = M.w (i + 1) r := by simp [xsw, op_mk, s1_mk, s2_mk, so_mk, w_mk]
      rw [e1, e2, e3, e4, sv_xsw_low h3 le_rfl (Nat.le_succ i),
        sv_xsw_low h4 le_rfl (Nat.le_succ i)]
      exact hv.w_eq (i + 1) hj r hr
    · by_cases b : i = j + 1
      · subst b
        have e1 : (xsw n M j).s1 (j + 1) = M.s1 j := by simp [xsw, op_mk, s1_mk, s2_mk, so_mk, w_mk]
        have e2 : (xsw n M j).s2 (j + 1) = M.s2 j := by simp [xsw, op_mk, s1_mk, s2_mk, so_mk, w_mk]
        have e3 : (xsw n M j).op (j + 1) = M.op j := by simp [xsw, op_mk, s1_mk, s2_mk, so_mk, w_mk]
        have e4 : (xsw n M j).w (j + 1) r = M.w j r := by simp [xsw, op_mk, s1_mk, s2_mk, so_mk, w_mk]
        rw [e1, e2, e3, e4, sv_xsw_low h1 (Nat.le_succ j) le_rfl,
          sv_xsw_low h2 (Nat.le_succ j) le_rfl]
        exact hv.w_eq j (by omega) r hr
      · by_cases c : j + 1 < i
        · have e1 : (xsw n M j).s1 i = tsw n j (M.s1 i) := by simp [xsw, a, b, c, op_mk, s1_mk, s2_mk, so_mk, w_mk]
          have e2 : (xsw n M j).s2 i = tsw n j (M.s2 i) := by simp [xsw, a, b, c, op_mk, s1_mk, s2_mk, so_mk, w_mk]
          have e3 : (xsw n M j).op i = M.op i := by simp [xsw, a, b, op_mk, s1_mk, s2_mk, so_mk, w_mk]
          have e4 : (xsw n M j).w i r = M.w i r := by simp [xsw, a, b, op_mk, s1_mk, s2_mk, so_mk, w_mk]
          rw [e1, e2, e3, e4, sv_xsw_late c, sv_xsw_late c]
          exact hv.w_eq i hi r hr
        · have e1 : (xsw n M j).s1 i = M.s1 i := by simp [xsw, a, b, c, op_mk, s1_mk, s2_mk, so_mk, w_mk]
          have e2 : (xsw n M j).s2 i = M.s2 i := by simp [xsw, a, b, c, op_mk, s1_mk, s2_mk, so_mk, w_mk]
          have e3 : (xsw n M j).op i = M.op i := by simp [xsw, a, b, op_mk, s1_mk, s2_mk, so_mk, w_mk]
          have e4 : (xsw n M j).w i r = M.w i r := by simp [xsw, a, b, op_mk, s1_mk, s2_mk, so_mk, w_mk]
          rw [e1, e2, e3, e4, sv_xsw_early (by omega), sv_xsw_early (by omega)]
          exact hv.w_eq i hi r hr
  · intro r hr
    have e : (xsw n M j).so = tsw n j M.so := rfl
    rw [e, sv_xsw_late hj]
    exact hv.out_eq r hr

omit hv hj in
theorem ind_xsw : ind n (xsw n M j) = ind n M := by
  funext i
  unfold ind
  have hp : (xsw n M j).pad n i ↔ M.pad n i := by
    by_cases a : i = j
    · subst a
      simp only [Model.pad, xsw, if_pos rfl, ↓reduceIte, op_mk, s1_mk, s2_mk, so_mk, w_mk]
      omega
    · by_cases b : i = j + 1
      · subst b
        simp only [Model.pad, xsw, if_neg a, if_pos rfl, ↓reduceIte, op_mk, s1_mk, s2_mk, so_mk, w_mk]
        omega
      · by_cases c : j + 1 < i
        · simp only [Model.pad, xsw, if_neg a, if_neg b, if_pos c, tsw_eq_iff c, op_mk, s1_mk, s2_mk, so_mk, w_mk]
        · simp only [Model.pad, xsw, if_neg a, if_neg b, if_neg c, op_mk, s1_mk, s2_mk, so_mk, w_mk]
  by_cases h : M.pad n i
  · rw [if_pos h, if_pos (hp.2 h)]
  · have h' : ¬ (xsw n M j).pad n i := fun h' => h (hp.1 h')
    simp [h, h']

theorem meas2_xsw (hlt : lexKey n s M (j + 1) < lexKey n s M j) :
    meas2 n s (xsw n M j) < meas2 n s M := by
  unfold meas2
  rw [ind_xsw h1 h2 h3 h4]
  have hk : lexKey n s (xsw n M j) j = lexKey n s M (j + 1) := by simp [lexKey, xsw, op_mk, s1_mk, s2_mk, so_mk, w_mk]
  have := lexWord_lt_of (B := lexB n s) (a := lexKey n s M) (b := lexKey n s (xsw n M j))
    (j := j)
    (fun i hi => by
      simp [lexKey, xsw, show i ≠ j by omega, show i ≠ j + 1 by omega,
        show ¬ j + 1 < i by omega, op_mk, s1_mk, s2_mk, so_mk, w_mk])
    (by rw [hk]; exact hlt) s (by omega)
    (fun i hi => lexKey_lt (valid_xsw hv hj h1 h2 h3 h4) hi)
  omega

end xsw

def LexNF (n s : ℕ) (M : Model) : Prop :=
  ∀ j, j + 1 < s → ¬ M.pad n j → M.s1 (j + 1) ≠ n + j → M.s2 (j + 1) ≠ n + j →
    M.s1 j < M.s1 (j + 1) ∨ (M.s1 j = M.s1 (j + 1) ∧ (M.s2 j < M.s2 (j + 1) ∨
      (M.s2 j = M.s2 (j + 1) ∧ M.op j = 0 ∧ M.op (j + 1) = 1)))

theorem nf_of_min2 {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (hmin : ∀ M', Valid n s g R M' → meas2 n s M' < meas2 n s M → False) : NF n s M := by
  classical
  have hmv : ∀ d t, d < s → TgtOk n d t →
      (M.Read n s d → ∀ r, R r → M.w d r = tval n M d t r) →
      (¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) → False := by
    intro d t hd ht htr hpos
    have hv' := valid_mv hv hd ht htr
    exact hmin _ hv' (meas2_mv hv hv' hd hpos)
  have htriv : ∀ d < s, ¬ M.pad n d →
      (∃ t, TgtOk n d t ∧ ∀ r, R r → M.w d r = tval n M d t r) → False := by
    intro d hd hnp ⟨t, ht, hw⟩
    exact hmv d t hd ht (fun _ => hw) (Or.inl hnp)
  have padOp : ∀ j < s, M.op j = 2 → M.pad n j := by
    intro j hj h2
    by_contra hnp
    exact htriv j hj hnp (op2_triv hv hj h2)
  have noF : ∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j := by
    intro j hj hnp
    by_contra hc
    have hF : M.s1 j = n + j ∨ M.s2 j = n + j := by tauto
    refine htriv j hj hnp (false_src hv hj ?_)
    rcases hF with h | h
    · exact Or.inl fun r _ => by rw [h]; simp [Model.sv]
    · exact Or.inr fun r _ => by rw [h]; simp [Model.sv]
  have padRd : ∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i := by
    intro j hj i hi hpi
    by_contra hc
    have hT : M.s1 j = n + i ∨ M.s2 j = n + i := by tauto
    have hnp : ¬ M.pad n j := fun hp' => by
      rcases hT with h | h
      · have := hp'.2.1; omega
      · have := hp'.2.2; omega
    have e : ∀ r, R r → M.sv n j (n + i) r = true := by
      intro r hr
      unfold Model.sv
      simp only [if_neg (show ¬ n + i < n by omega), if_pos (show n + i < n + j by omega),
        show n + i - n = i by omega]
      exact pad_w hv (by omega) hpi hr
    refine htriv j hj hnp (true_src hv hj ?_)
    rcases hT with h | h
    · exact Or.inl fun r hr => by rw [h]; exact e r hr
    · exact Or.inr fun r hr => by rw [h]; exact e r hr
  have ord : ∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j := by
    intro j hj hnp
    by_contra hc
    by_cases he : M.s1 j = M.s2 j
    · exact htriv j hj hnp (same_src hv hj he)
    · exact hmin _ (valid_sw hv j) (meas2_sw hv hj (by omega))
  have pre : ∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j := by
    intro j hj hp1
    by_contra hnp
    exact hmv (j + 1) 1 hj (Or.inr (Or.inl rfl))
      (fun _ r hr => by rw [pad_w hv hj hp1 hr]; simp [tval]) (Or.inr ⟨j, by omega, hnp⟩)
  have rd : ∀ j < s, ¬ M.pad n j → M.Read n s j := by
    intro j hj hnp
    by_contra hc
    exact hmv j 0 hj (Or.inl rfl) (fun h => absurd h hc) (Or.inl hnp)
  refine ⟨pre, padOp, noF, padRd, ord, ?_, ?_⟩
  · intro j hj hnp
    rcases rd j (by omega) hnp with h | h
    · exact h
    · exfalso
      by_cases hl : M.pad n (s - 1)
      · have hall : ∀ m, m < s → M.pad n (s - 1 - m) := by
          intro m
          induction m with
          | zero => intro _; simpa using hl
          | succ m ih =>
            intro hm
            have := pre (s - 1 - (m + 1)) (by omega)
              (by rw [show s - 1 - (m + 1) + 1 = s - 1 - m by omega]; exact ih (by omega))
            exact this
        exact hnp (by
          have := hall (s - 1 - j) (by omega)
          rwa [show s - 1 - (s - 1 - j) = j by omega] at this)
      · rcases rd (s - 1) (by omega) hl with ⟨i, hi1, hi2, _⟩ | h'
        · omega
        · omega
  · intro hs
    by_cases h6 : M.pad n (s - 1)
    · exact Or.inr h6
    · rcases rd (s - 1) (by omega) h6 with ⟨j, hj1, hj2, _⟩ | h
      · omega
      · left; omega

theorem lex_of_min2 {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (hmin : ∀ M', Valid n s g R M' → meas2 n s M' < meas2 n s M → False) : LexNF n s M := by
  have hnf := nf_of_min2 hv hmin
  intro j hj hnp ha hb
  have hnp1 : ¬ M.pad n (j + 1) := fun h => hnp (hnf.pre j hj h)
  have f0 := hnf.noF j (by omega) hnp
  have f1 := hnf.noF (j + 1) hj hnp1
  have l1 := hv.s1_le j (by omega)
  have l2 := hv.s2_le j (by omega)
  have l3 := hv.s1_le (j + 1) hj
  have l4 := hv.s2_le (j + 1) hj
  have h1 : M.s1 j < n + j := by omega
  have h2 : M.s2 j < n + j := by omega
  have h3 : M.s1 (j + 1) < n + j := by omega
  have h4 : M.s2 (j + 1) < n + j := by omega
  have o0 := hv.op_lt j (by omega)
  have o1 := hv.op_lt (j + 1) hj
  have o0' : M.op j ≠ 2 := fun h => hnp (hnf.padOp j (by omega) h)
  have o1' : M.op (j + 1) ≠ 2 := fun h => hnp1 (hnf.padOp (j + 1) hj h)

  have hx : lexKey n s M (j + 1) < lexKey n s M j → False := fun hlt =>
    hmin _ (valid_xsw hv hj h1 h2 h3 h4) (meas2_xsw hv hj h1 h2 h3 h4 hlt)
  have hK : ∀ y z : ℕ, y < n + j → z < 3 → y * 3 + z < 3 * (n + s + 1) := by
    intro y z hy hz; omega
  by_contra hc
  rcases lt_trichotomy (M.s1 j) (M.s1 (j + 1)) with e1 | e1 | e1
  · exact hc (Or.inl e1)
  · rcases lt_trichotomy (M.s2 j) (M.s2 (j + 1)) with e2 | e2 | e2
    · exact hc (Or.inr ⟨e1, Or.inl e2⟩)
    · by_cases e3 : M.op j = M.op (j + 1)
      · have hw : ∀ r, R r → M.w (j + 1) r = M.sv n (j + 1) (n + j) r := by
          intro r hr
          have hs : ∀ k, k < n + j → M.sv n (j + 1) k r = M.sv n j k r := by
            intro k hk
            unfold Model.sv
            by_cases h6 : k < n
            · simp [h6]
            · simp only [if_neg h6, if_pos hk, if_pos (show k < n + (j + 1) by omega)]
          rw [hv.w_eq (j + 1) hj r hr, hs _ h3, hs _ h4, ← e1, ← e2, ← e3,
            ← hv.w_eq j (by omega) r hr]
          unfold Model.sv
          simp only [if_neg (show ¬ n + j < n by omega), if_pos (show n + j < n + (j + 1) by omega),
            show n + j - n = j by omega]
        obtain ⟨t, ht, htw⟩ := copy_tgt hv hj (k := n + j) (by omega) hw
        have hv' := valid_mv hv hj ht (fun _ => htw)
        exact hmin _ hv' (meas2_mv hv hv' hj (Or.inl hnp1))
      · have : M.op j = 0 ∧ M.op (j + 1) = 1 ∨ M.op (j + 1) < M.op j := by omega
        rcases this with h | h
        · exact hc (Or.inr ⟨e1, Or.inr ⟨e2, h⟩⟩)
        · apply hx
          unfold lexKey
          exact lex3 _ _ _ _ _ _ _ (hK _ _ h4 o1) o1 (Or.inr ⟨e1.symm, Or.inr ⟨e2.symm, h⟩⟩)
    · apply hx
      unfold lexKey
      exact lex3 _ _ _ _ _ _ _ (hK _ _ h4 o1) o1 (Or.inr ⟨e1.symm, Or.inl e2⟩)
  · apply hx
    unfold lexKey
    exact lex3 _ _ _ _ _ _ _ (hK _ _ h4 o1) o1 (Or.inl e1)

theorem exists_nf2 {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} (h : ∃ M, Valid n s g R M) :
    ∃ M, Valid n s g R M ∧ NF n s M ∧ LexNF n s M := by
  classical
  have hex : ∃ m, ∃ M, Valid n s g R M ∧ meas2 n s M = m := by
    obtain ⟨M, h1⟩ := h
    exact ⟨_, M, h1, rfl⟩
  obtain ⟨M, hv, hm⟩ := Nat.find_spec hex
  have hmin : ∀ M', Valid n s g R M' → meas2 n s M' < meas2 n s M → False := by
    intro M' h1 h3
    exact Nat.find_min hex (hm ▸ h3) ⟨M', h1, rfl⟩
  exact ⟨M, hv, nf_of_min2 hv hmin, lex_of_min2 hv hmin⟩

section formula
variable (n s : ℕ)

def lexBase (j : ℕ) : List ℕ :=
  [P (ix n s 7 j 0), P (ix n s 1 (j + 1) (n + j)), P (ix n s 2 (j + 1) (n + j))]

def fLex : List (List ℕ) :=
  (List.range (s - 1)).flatMap fun j =>
    (List.range (n + j + 1)).flatMap fun a =>
      ((List.range a).map fun b => [Q (ix n s 1 j a), Q (ix n s 1 (j + 1) b)] ++ lexBase n s j) ++
      (List.range (n + j + 1)).flatMap fun c =>
        ((List.range c).map fun d =>
          [Q (ix n s 1 j a), Q (ix n s 1 (j + 1) a), Q (ix n s 2 j c), Q (ix n s 2 (j + 1) d)] ++
            lexBase n s j) ++
        [[Q (ix n s 1 j a), Q (ix n s 1 (j + 1) a), Q (ix n s 2 j c), Q (ix n s 2 (j + 1) c),
            Q (ix n s 0 j 1)] ++ lexBase n s j,
         [Q (ix n s 1 j a), Q (ix n s 1 (j + 1) a), Q (ix n s 2 j c), Q (ix n s 2 (j + 1) c),
            Q (ix n s 0 (j + 1) 0)] ++ lexBase n s j]

def enc2 (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) := enc n s g rows ++ fLex n s

end formula

theorem s_fLex {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (hn : NF n s M) (hl : LexNF n s M) : ∀ c ∈ fLex n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fLex, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain ⟨j, hj, a, ha, hc⟩ := hc
  have hj1 : j + 1 < s := Nat.add_lt_of_lt_sub hj
  have hj0 : j < s := Nat.lt_of_succ_lt hj1
  have hb1 : ClauseSat (val n s M) (lexBase n s j) ↔
      M.pad n j ∨ M.s1 (j + 1) = n + j ∨ M.s2 (j + 1) = n + j := by
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [lexBase, cs_cons, cs_nil, litVal_P, v_pad, v_s1, v_s2, or_false,
      beq_iff_eq, decide_eq_true_eq]
  have happ : ∀ c', ClauseSat (val n s M) (lexBase n s j) →
      ClauseSat (val n s M) (c' ++ lexBase n s j) := fun c' ⟨l, hl', hv'⟩ =>
    ⟨l, List.mem_append_right _ hl', hv'⟩
  have hfront : ∀ c', (∃ l ∈ c', litVal (val n s M) l = true) →
      ClauseSat (val n s M) (c' ++ lexBase n s j) := fun c' ⟨l, hl', hv'⟩ =>
    ⟨l, List.mem_append_left _ hl', hv'⟩
  by_cases hesc : M.pad n j ∨ M.s1 (j + 1) = n + j ∨ M.s2 (j + 1) = n + j
  · rcases hc with ⟨b, hb, rfl⟩ | ⟨c', hc', ⟨d, hd, rfl⟩ | rfl | rfl⟩ <;>
      exact happ _ (hb1.2 hesc)
  have hnp : ¬ M.pad n j := fun h => hesc (Or.inl h)
  have L := hl j hj1 hnp (fun h => hesc (Or.inr (Or.inl h)))
    (fun h => hesc (Or.inr (Or.inr h)))
  have hop0 := hn.padOp j hj0
  rcases hc with ⟨b, hb, rfl⟩ | ⟨c', hc', ⟨d, hd, rfl⟩ | rfl | rfl⟩ <;> apply hfront <;>
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left, litVal_Q, v_s1, v_s2, v_op, Bool.not_eq_true', beq_eq_false_iff_ne,
      ne_eq] <;> omega

theorem enc2_sat {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {M : Model}
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (hv : Valid n s g (· ∈ rows) M) (hn : NF n s M)
    (hl : LexNF n s M) : ∀ c ∈ enc2 n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  rcases List.mem_append.1 hc with h | h
  · exact enc_sat hrows hv hn c h
  · exact s_fLex hv hn hl c h

end Lk

namespace Rp

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents PEqualNP.Outside.L_meta_5562 PEqualNP.Outside.L_meta_5562.Lk

theorem promise_lower (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ) (hrows : ∀ r ∈ rows, r < 2 ^ n)
    (hU : ¬ FormulaSat (enc2 n s g rows)) (C : Circuit) (hC : Monotone2 C)
    (hev : ∀ r ∈ rows, C.eval (List.ofFn fun i : Fin n => r.testBit i) = g r) :
    s + 1 ≤ C.size := by
  by_contra h
  have hv := valid_ofCirc n s g (· ∈ rows) C hC (by simp only [Circuit.size] at h; omega)
    (fun r hr => hev r hr)
  obtain ⟨M, hM, hnf, hlx⟩ := exists_nf2 ⟨_, hv⟩
  exact hU ⟨val n s M, enc2_sat hrows hM hnf hlx⟩

def row44 (u v : Fin 4) : ℕ := 2 ^ (u : ℕ) + 2 ^ (4 + (v : ℕ))

theorem row44_eq : ∀ u v : Fin 4,
    (List.ofFn fun i : Fin (4 + 4) => (row44 u v).testBit i) = oneEach u v := by decide

def rows44 : List ℕ :=
  (List.finRange 4).flatMap fun u => (List.finRange 4).map fun v => row44 u v

theorem rep_lower44 (A : Fin 4 → Fin 4 → Bool) (s : ℕ) (g : ℕ → Bool)
    (hg : ∀ u v, g (row44 u v) = A u v) (hU : ¬ FormulaSat (enc2 (4 + 4) s g rows44)) :
    ¬ RepSizeAtMost A s := by
  rintro ⟨C, hC, hs, hr⟩
  have hrow : ∀ r ∈ rows44, r < 2 ^ (4 + 4) := by decide
  have := promise_lower (4 + 4) s g rows44 hrow hU C hC (by
    intro r hr'
    simp only [rows44, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at hr'
    obtain ⟨u, v, rfl⟩ := hr'
    rw [row44_eq, hr, hg])
  omega

end Rp

noncomputable section Cert

def g (r : ℕ) : Bool := [17, 18, 20, 24, 33, 34, 66, 129].contains r

theorem hg : ∀ u v : Fin 4, g (Rp.row44 u v) = (4475 : ℕ).testBit (4 * u.val + v.val) := by
  decide

def cK : List Nat := keysOf 0x1000c0000000000000007f80010040000000000003f80000000000000000003f00000000000000000007c001f020000000000001e0000000000000000000e0000200000000000000c0000401000880000001000b74010080810422c000000000000000000000000000000000001f00080000000000007f00000000000000007e0000000000000000f80078000000000003c0000000000000001c00000000000000018002f000000000002001be0909128845800000000000000000000000000000fe00000000000007e00000000000007c0000000000000f0000000000000380000000000001800802000000010021c000000003c001effdfd00000081042258007fffffffffffffffe003fffffffffffff801fffffffffff007ffffffffffdffff3cf7ef38102020040810100202002002002007d408c3f9c387119c387119c468d1a3b88d19c307119c207119e7ead5bfbccd79c32ed59c30f19bffe8d7fffefdf99306519830e51b9f6ed1bffaeff9820611980169ddbd7cd9fbffedda80014000a8003800280014000b80028002fa01ea00f4007a80bd5f9f422f5107cf728007490e8a0e843a884080e891e053f827f68f751eb63ffe7ff0ff71ef63a21480eb827daa10080eb66e93ffdffe5dd6f73ffdfc6fff7ffb884108a0f3284008ff9e13fe7fcff8f67fe686ff9ff22080085321000a46b21978de773f9fcfe7f0a80054002a080e800a80010002e240ba00fa087e601f100f808fdc07e823fd01fff0bba06802ca02f18b8400002a902858fc36f7ebf742ff9fff1f823ffc3ff82204d02ff0d98a100082270fb8bfc7fe1dd0ff8ffc5fe3ff1ff8890100a4738840087fc6589f1fe37c768ff1fe3fc7fa20002801a1098243ba0dfedd76bfdfeff7fffff 6467

def cP_0 : List Nat := [
0x10e0c14c837f80005dda1c1429606ff0000bab038205290dfe000174607030aac1bf800021db0e04155437f00002a661c042aa06fe000021dc38005400dfc000260506ff0a5c14881ff052f0a8210f029805570a8a11f429885580a94130c29905590a9e13e82ad05530a46149029285260a4e14a0295852d0a54000308586fe,
0x100017bbe45e07130a7e1bfc0002f7b0e2414f837f80005df61c4429e86ff0000baec388053c0dfe000174d070f0a761bfc0002f730e1c14e837f80005de61c3429c86ff0000bacc38605380dfe0001749070b0a6e1bfc0002f6f0e1414d837f80005ddc1c2429a86ff0000bab838405340dfe000174707070a661bfc0002f6c,
0x10e2a1c080005eef0e2c001028484f207a40e78380070a0e0600010e88715001218fc31f063d0c7818ec31d06390c7015b02b505680acc155c2ac05590e021bf80005eef43861c5000481ba03e207900f181d803ae06cc0d904fd0a34143828404f8000813f02b6056a0ad015982ab85580ab21c0438307100e181c283828700,
0x10e060000a90871d0008143827881e3033a1c0038607030000547c38e00040a1013c40eb819c0e001c2838180002a3a1c6c00204fe09f0070c0d907000e0e1c14000151b0e34154838b00003f7a1c642a8871600004c5438c05500e2c000032d87170ace00382b4855707720ee01db83b6076a0ed02b585580e281c4c2b68559,
0x10420150c000267c4dfb6268caa87220e3e16282c1857d00016268ca98721000010581f9822a0410000131ea6fe000c658439000050af015d02b8856f0adc150c000589a196832d865c19530e3e001400f802b005400a401403fb0806000020003fe000099f137e8cba196832d865c404c0e3c001028d04f103e206783800710,
0x10a1213f40dd04f6000813d00d487040e001c1838507050000548d0e987270e3c163c2c405820428150c000267c4dfb6268cae87260e3c16382c385810426150c000267c4dfb6268cad87250e3c16342c305800424150c000267c4dfb6268cac87240e3c16302c2857f0422150c000267c4dfb6268cab87230e3c162c2c2057e,
0x10e0e1c3038507050dfc000065d000343b221d4a96152e0cae4bfc3950008027e04e40b781710e30000144c931273f44c08982130626104c2898739780e52001805500a90150000076c0ed61d8c3b207650ecc1d9cd3bc394000007f80fcc107020700141c9839287240e461c8839087200a880ff82b383d307740eb81d304f9,
0x10cc6198432f042304a407b40da854309f0146000205170e1e1c003828000b134000e3f541e91dac3b1c65a152b0e5600140238038006800cc0190031006000bc20c0409080a077c0e501c40012072428605030a000f681e503c509b81338265017602ae053432a81b309f0076028401e40a1c1c6c38d071c0e3a1c043858708,
0x10e181c5800013102624876432c9fab0e5e003431a86340c6418c4318062f0c5c1c6438b00003f4c7ec8fdc1fba26261cb8001048b08f60b741600000087ca26555a285a54ee7674396800c0be817cc2f905f10cae0aac150054e0ab00c301868000b56c4c4141c952c43a87ee21d91d8e3b190e90396000500a619d43378666,
0x10e2c0000fdd13123f52767439900040a1614241ed03d809bc136c380070b0e140002351c5c6723c876432c87310010188c30d06120c16181430005fc0bf217dc2fb07180e2c00009891fa70e6000200a68123099a12e81e283a309fe13c8002050f07bc138430e06140c1a181c30105fe0bf60de01a703210e301c1c3818700,
0x10d5a1a9c351069a0d2e1a5434785bf000e1bcc37506e40dbe1b5436906cf0d9415382a6854c0ab015242a400080bf017e82fe86010c0c1830309861b0c481cc838c071600007ee89891fa921e96ad839980070d861bf437986ea0dc81b7c36a86d20d9e1b282a685580ac000202fc05fa0bfa1804303060c0c26186c3120718,
0x10c18184c30d86240e641c6c38d071c0e3a1c04383070c0e141c1438007170dfc1c6038b00003f744c48fd490f40e6a003832a06510ca0193c327064d0c98192c32c85690ace155c38a87020dfc1c580005ab743b01cd033e800200161ae834406860d081a08340067f0cfc164800600060d6a1b0836086c00d7e1af835e86bc,
0x10c36184c30606060c0217f42fd05f80e301c580001fba26247ea439b000c0d761b0436006bf0d7c1af435e05bf000e1ba837206df0daa1b4836786ca0a9c15342b50009037407900ec01b309fa143828404f8000813f01df04c500061cc432a87340acc15782ae85680aae1ccc1a0836a06e405d800405f80bf417f43008606,
0x1b56c7ee098815302a4c54a0a9215223b3854a8a960739042a1c7800507200cea19bc33507210a88150c21007260e4a1c90391872203b206d40d6056603ca06f40003b94782ced69e0abb551dac3b1cdbf152b0e7000302fa05f30be417c42f805ef0bdc17b42f605f50a9c15602af800021ea1cdc2ac06fd0abe1cd40040624,
0x1085a0004122842e0e70068c1d007390cae1ce802c80060d6a1ab435386a20d341a5c34a868f0a8e15200d981d803c806e839b8000b56c7ee098815308fb8ee51e0b3b5a782aecd5daabb373b38438c39d8001088610e40e301b700d201e400002227728ecdc763952d0e74192400486570dfc1c6c38d071c0e3a1c0439b8000,
0x10856023c02d00000444a0e548d0ec90e7e11b4001047a07440ec4000043e90791f71b7eb75d874a875c39f0002090a11e80e401b9018c0364000043e7728ecdc871952f0e7a00001fe03ee041c080000507200e42151021007260e4a1c90391872203b206d40d601a30acc07940de80007728f059e0abb5a76aaecd4a95873c,
0x10036007c00a80140024004400803f607f60fc400003ee0b220820100800a0e841c9839287240e461c882a105430a881c8400026fdb134987531ea67c0e8600001fe03ee041c0800000261d000c99f0caf87420002119021580ac00b80000111283950cc3b343a0800108b210ac04d805b0000088941ca85e1d961d000008452,
0x100360014023041c0e8a005800a801007e207f82a185440e420002c4d26234c3a98f4cb00005195c32d0cab195c32b032c1fb60746001408b8115800032c46548cb0195632b86560cad3f730e8a00140230023002a00500090011002010701fe83f100000fb82c8822f041e08042a1054300016269311a61d4cfa65843a20005,
0x1027e04e809c84bb096c130000184c20e301c5c0001312513299f5638ac9159a118843a5072e0c6c18cc31686580e2c0000a975cd23f7487583a4800c0bd417a02f305e50bc815380005cd23b147658ecd1d9c3b2443cc3a400070bce17602a680c70190032406500cb019a1cdc0005cd221c4dd74ec98747040e00281fb0579,
0x1098212e800184b706680ca4238846b018402e0003874805800af815d82b808f20d003a503b307540e8c00703a507320e681cd839c073a18dc2a680c70190032406500cb019a1d1c2b283ac075e0eb838c07170e6e1c54381071600011f74fdda1d621c4a265baea67d087720f23fe874b001004c40948127024a0490091813d,
0x12a5c875944ca67d907a1d3400706550c9e00240d481e403b006d40db81b309ec143828404f8000813d43a583ae075e0eb01cc839a07360e701ce87150e041bf838d871a0e381c7438087040e181c28382870000011f74fdd952e43ac438944cb75d4cfa10ee41e074c001004c409e813f027204a40940127024a049009184be,
0x100007eed44ca67d43b2b1c56682ab50e9e003832a064f0cb20e641cd039b07380e7438a87020dfc1c5800047dd438487510e921d80e9c003832a86530ca400240da81b7078006a40d101a1034013dc27f84f409e2001027c83ad07320e681cd839c073a1c5438106fe0e361c6838e071d0e021c1438387040e061c0000047dd,
0x1057013d423c874b0e98000823d0747019a032c06500c90190031c2a6054d0aca1d3c1d983a30e9c0eb81d783ac0e6e1c1038000008fba7eed44ca67d90788758871375d0ea000240d481e403b006e40da81b7036613d8287050809f0001027a83aa0e940d0031b86550e361c6838e071d0e021c10386070a0e0a1c0037f0716,
0x1001804581890107020c0c0017f02f105d603e807a02c0057c0aec15c04ad095c127c2500498092e11ec2a6854e018c033006707370001734944ca67d5568dd7159b2a7a550410f43a90007016e030c06000bf017c02f423584710e6e000087b10e221dc43c953aaa5508761d4423880c20360001c27b074800080b0015f02bb,
0x102880ef800404fd027a04fc09c81290250049c092812402460d300e084c1097411f800180d4096e001c19480c3018002fc05f00bd0ea211c431b854d018c033006700020ea407d028d01e80a1c0774284074f0a98159438c07060e2e1cdc385070c0e201c580001fbb513299f50ecac7159a0dd70a97887554ea1d4c2e68007,
0x10e180000fdda1d92a5e21cc32caa7b0eac0fa02758519072007d038800003f768764a9788730cb2aa0c3aa800802f804c4098012f027a04fc09d013902e205bc27004be0982136800184bc075413d819a01b00ea60f781ec050f0a1218dc38c07170e081c30385071600007eed44ca67d43b2b1c5668375c2a5e21d43aa04c9,
0x105fc0c000005cd254aaa9d421e9d8a3b2c7668ece43ca3b2043943ac8729027a000098928994cfa4c08982130826144c19cfd39780eb00f6026d850706e207743a907560eaa00083a881a709e206c027a00ce019803182a6854c0aca1c28382070300007eed44ca67d43b2aad1bae152f10e619643ab83de09c214341be81e8,
0x10eb800302f105df0bb8001c3ad0759022c0c4825684ae0a9c0bf818004a0020c041c24f80020ea215342a607370001734887110ee21e4a95553a9d8a3b2c7668ece2a7a55041d6c159800c08ec17342e500c00a9c0bf81800000b9a4a9d421e9d8a3b2c7668ece43ca3b2043ac3ad000c05600a9c23b04700b8202f4059854e,
0x13b2c7668ece2a5521dc7648ec8075e00180b0015f047b0eb8001028401dd092e17882f085df0bbc17702ed80fa0a9c159417f03000e001c28000267d3f76a264a97843d879443c43ae84f7076606e43a783a309e4003832506410c92191432306420c90191c32186440e0a1c0837f07150e06000133e9fbb513254bc439aab5,
0x1020c041c24f875d09400ae015d82be05801cdc38180004cfa7eed44c952f087aa9e953a90e221e5101043987600166001c23805cc0b900a8c2a687370001734821e90e621d843c087110f254aa43b8ec8875f054e003023805c6016a001c3ad07590a9a153817f03000e6e0002e69043d8794439887610f054ea43888791d8a,
0x103701d7027f00040ec215302b287070e00000133e9fbb513254bc21eaa7a0ec606c027a07600e080000fdda8992a5e10f553d440421c499f443990f20ec41d4823d01f403ba06e428d050809f01c403850705000099f6e6928992a5e10f553d08750ec211d805f82b0000e1d783ad07590ebe033023d01a70eb813c42a68565,
0x150b6a11c764264250be087c3b300070b96171000607640230045818a0312095a12b82a6854e01e803e824b82eb05e2126039b8000b9a410f553a90e23b147658ecd1d9c21dc43c959b2a820eca02f800384760b9a0ac02a680f401f4045808c07370001734821eaa7521c443b887937de6e54764c3b207620e7a033823d047b,
0x108f61d8c380070c000099f544cc4053f7654bc21e8769001616b02d585aa0b5200183b3825304a2093c2a4054904ec09f00005ab61dac3b187670ecc1d943b221350ed44cfb07a03b4000b0b4c16942d205a30a9209d813e0000b56d09a8db71b7a36fc3b443b387280142020c03d807a00f2118022c04460886000076c283b,
0x102621d600938125024804e826d04ba0982000c25b8637018c033006707370e2e1c58000267d513243d8fdd843b6eb917016682d525922b545638876b0caa1d3800484f3033e06cc27c03ac09f2076028401e40a1c1bf838d871a0e381c7438087030e181c2838280002a5c21d4a96152a43a88749d9a076a000814383ae01e8,
0x10a1c031806600ce0e6e1c5c38307040e361c6838e071d0e021bf8386070a0e0a1c4038b00004cfaa26487b1fbb2a5c10ec43ab75c8b8087643b68729031805f00bd813d0274049827504e009b4130425c80004cfaa2649892cd05aa4b25964f2c700cb21db000380d40186030005f80be017a11f8238834c0668132425f0144,
0x151324c496682d52592cb279648c5e00ede003832a064f0cb21c5438106fe0e2c00010e121ce43a887490e221c6439887210ec076e000e030c06a00c0017e02f805e847e08e20d3019a04c50978000c3b6076b077c0ea827e84f6037406a400483e807bc0f601d986550c6e13e4284850f0a3606cc0db81b509f0076028401e4,
0x13b34767087110ee21e443c087510e821cc1dc8153800c08e0174c2e905d10ba0173c05b854e0001734952a843d3b147658ecd1d9c21da1dc42798004074613c425b81a706521c0c380000043b27eec32b952f54a81dc00040131031805f00bd817102de04f409f813a027212f827504e009b4130400184bc0e301c5c000267d,
0x1054a11d823805c70b8c02fc05a854e0001734821eaa553b147658ecd1d9c54ea7640874877400180a9c15282a30ec811c02e205c3022a03d405a054e0001734953aaa55087a7628ecb1d9a3b38438887710f221ce1dcc00602a505440c0417f84700eb21704059875f000e15342a707710e6e0002e692a7554aa10f4ec51d96,
0x10bbe17782ee85dc0eea07040d804fb09e8001028702c0057c0aec15c01e80ed21d8c2a7056a0e0c1c10380070c000054bc21e90e221e443b8fddaa554cfaa2643bb000c058c0c04241875a0b9a172c2e500d30ee41dd03af854e0ee21dcc0005cd2087a438887910ee54aa7628ecb1d9a3b38a9d559a90f00eea003015802a7,
0x10492090c120823f047c10d8218059400c401682a48000b56ca16541c822136dc6de8dbf0ec90ef2002c2d905b10ed01ddc14a829305240a4423107280a901524127825104a6000133edab6508e08860f40ec61dac3b387660eca1d901de0005827904f00a441490293052a0000dc01b6e36f46dfa0cbc26b0eee00302f105e0,
0x10a1c069439b87080e0c1c1038d871a0e381c74380870c0e141c1438c87160000a0e032b95303f7410ec989130f10eaecd4a951d9d0ef804f42600008068018dc38c0716000099f432b930026044c10984130a26184c4098312fe556ab340fdd877b000c16bc2d405a20a900002d5b0ed61d8c3b387660eca1d906dc43bd000b,
0x1001609601260248088410d82cb807300c615240005ab650b2a4641109b6e36ec6df8dbd1b701d961df400380e201a8030c06100c0017e02f805e848a08fc11c41e403bc0750140c27e84f6039206e80d480090e92069c23606fc055415342ac05450862003431106200c3e187030e87360c3c1cc031081b309f0076028401e4,
0x100016ada2023b94782ced69db11d8c3b307638eca1d908788b241daa9fb921d6b1c5639952d0f0206c027a074900080ec027c87040e001c140005cd23f74a9d155a483d0f00000c26004c10e2e0002310b97959a01dfc00582580498110821b059b0b34166403a00640a920002d5b285952320884db71b7636fc6de8766877e,
0x10f06003431106210c40187c30f061d0c38186c30d07190e2c0000fdc1fba261e1e08005828804f80944350845a08a610e800084320b40167c2cf059d0b380194003073a038e1d043a0073f06a60c9c26584b700061ae435886ab0d4c003025e82b7066607cc0f381db035c06dc2a385480a92153815c02bb0b9a156039b8717,
0x1069e18982a600b2018c195438d871a0e381c7438087060e081c1c38187170e181c2838286fe0e2c0000fdc1fba3f5b7349c9c39fb21c76ad90ec88750f0a1cc0316871600007e9c3c2000d0c5618a831406270c4c189400406fa0df21be037b86f60dea1bd037987360e5c1e0838c87160e300002e691fb821e67ee8fd91fa6,
0x10c96196437f0716000087603c404f200080e8c3c287030e000000fdc1fba3f5b7349c9c39fb21c6b1c2d5b21d90f0e000c25d04b70e2e00022e0391858e21e1815581a50e7c00243a4873c03521cf439d84fd09ec140027983be07540f141d184c50976132c25b800309b407901ec01d803661438284850809f213e01910343,
0x10a000f14265834f03521cf027e83be098a0d0c28704f6075412ec00184da07b014240b7812e09e6142027c000409e40e8c3c301230644153038d871a0e381c743c487010f101c1438007030e141c1038b870c0e0c1c1c0001fad26027ee0fdd5cd221c61e2832a86fe0f100000a9887890edc194c32906510ca01938326864c,
0x107b014240b7812e09e6142027c000409e40e8c3c3012306441cdc38d871a0e381c743c487010f081c1438007030f101c2838207170e181c1838387100e2c0000fd693013f707ee88755cd20f181d6c0d381f403d006c00003b5a76c4ecd5daadcd221e443b88711d8a3b387658ecd152f0f1600242b4073d0f0e06cc0ec01e4,
0x10ab01c6c38d071c0e3a1e2438080002a4c54a0a9215222a55734c3c680060e741cfc35b06ae0d501a8c34d86980d2c15202a381a503b615a0004878b0d9a1b2c36705c0000e1e2837586e50dc01b4c36807830a9a18c019c83360a3406cc0ec01e40a000f14265834f03521cf027e83be098a0d0c28704f6075412ec00184da,
0x13b147658ec91d9c21e61e4000104a70910043806d0000087ca95953190e50f1e1e3036b06300f1a1cf027e83be098a0d0c27981a909ec0ea825d800309b40f60284816f025c079028701d80a1006cc27c000409e40e8c3c3012306441c1438007030f101c2838607040e2e1c1838b00003f5a4c04fdc1fba0f1c00242b4056a,
0x10a9815342a407370001734959a2b3a54e8a95152d2ab45586a98d541dab650cca0fc7640eca1d983b1887210ea0f24001835c06b00d541a9434e80070f200c5c189830f0614047408d0119022a044c25604a8096012ac2a685480e6e0002e692ac354c6aa0ed5b28661d903b287660ec621c843a821d87910e9017ac0005cd2,
0x10976000c26d03d80a1205bc09701e40a1c076028401b309f0001027903a30f0c048c191071b0e341c7038e87890e021c1438007030f101c2838607040e2e1c1838587070e200000fd693013f761e4c00306b80d601aa8352869d000e1e4008502fc05ee0aec15c00d60198030405904a5093811ec240847a08e811b80010791,
0x10f101c5c381870c0e141c14380071600007eb49808794000412ac2370117016c1e483c7873a0e821d0039f854703c206940f981e703b615a000481c1071e0e281ca834006ee0d581950335070a0d34196033607000e181c583910a3414001e284cb069e14301ed04dd06e615303c6873c09fa0ef8262834309e606a427b03aa,
0x10f2a125c07a0002000e1d440d3873d03ba06c000481a506501e3837586e50dc01b5836986d00de81e4c2a6854c0f1a1cf00d484fd09ec14001df03aa078a131425d84cb000613680f203d803b006cc279850e0a12142027c000409e40e8c3c3016f025c048c1910343069e18c039b871b0e341c7038e87890e021c183820707,
0x109f0001027903a30f0c05ec097812400101b28191034f0bfe180c304060e0c2a187431306300f28153005e80da0e6e1c6c38d071c0e3a1e2438087040e0e1e2038b87030e201c3038507050e001c6038b00003f5b734887295282a4854a8a9315223f741e583a481dd0788125c24400da01e80002e6910e53f74f05a3ef043d,
0x107540f7827b050f000813d038b87880e081c3038000008bc0e4fddaa07980f1e0e281ab034f070c0000fd6843e21ca7eec3cb80060d6c1ab835406a30d361ce816a87410e801cfc2a40547090e07180d281f303ce076c2b403c400121d240d8047100041e5427b050007540f1425d84cb000613801ef04f30a34143c2870508,
0x121ec439087410ea21d843b887810f26dfe1e683cb01ab0e7813f41df01e40988000c27003de09e6143c287050809f000100d501a909e41e601d1878602f6050809200080d941e5c191032c0bfe180c304060e0c2a187431306300f28153038307880e2e1c0c386070a0e0a1c0038c071600007eb6e6910e50f32000c25e04e0,
0x107d0146c1c583220a1013e036a06d70dc21b9837606f50c601e2439b871b0e341c7038e87010e2c1c1438507030f101c5c38807040e181c1838380003f5b7348a91087526067ee8a97079c000c1a9035486b70d5e1a7036886300a901cdc38b00003f5b73489819fbab56c3b207650ecc1d8c439c3cd800701b6036439b8000,
0x106581cdc38207880e2e1c4038387030e1c1c1438b00003f5b7348a91087526067ee83ce82ab0e7c1cec06300b2000e1e6c39d07410e801cfc1998547034a07cc0f381db035c15a000487490c4c15302a6879909f214680d981d803c814001e284cb069e1cf027e83be098a0d0c28704f6075412f019604f3074612dc00184eb,
0x107d0146c1c583220a1013e038d871a0e381c743c487010e0a1c2838187880e2e1c40382070c0e0c1c2c38380003f5b7348a9108753f761e78252810a0004001c3a881a70e7a07b00d8079c0dea1bb037306e10dae1b50318054c0a9a1e6427c051409e60e8c25b83220a000f14265834f09ec0ea825e000309d60fa028d838b,
0x10e2c0000fd6dcd22a4421d43cf8002095611b808b80b60f241ce83a087400e7e151c0f081a503e6079c0ed8568001207041c7838a072a0d001bb832a066a0e141a6833607000e181c8854c0f3214680d981d803c814001e284cb069e14301ed04dd06e61cf027e83be098a0d0c28704f6075412f019604f3074612dc00184eb,
0x10de61ba837206df0daa1b4836780080f3a1e7839e04fd09ec140027983be07540f141d184c50978132c25b800309d60fa00f201d80366146c287050809f00c881960343069e0e2c2ff86030c10183830a861d0c4c18c03ca054c0a9a1e643c4871b0e341c7038e87010e6e1c6038307040e0e1c0c3c407170e201c303850705,
0x109d60fa00f201d80366146c287050809f000103d0038b06860cb019107060e081c0c3c407170e201c3038507050e000000fd687a102ec002026f012400061e1825b83da0746142c279032206e617fc30186080c1c185430e86260c601e5038c07170f101c2c381871600007eb443987a006661cec0d7056800121b1039e8007,
0x1034e1cf400485660aba15a02ab81b309f0076028401e40a1c15302a687a20e6e1c6c38d071c0e3a1e24380870c0e141c1400008758b804c49d9a92ff766e548ad5b87a30acc155c3c68558036613e00ec050803c81438386070a0e0a000043a9522b9a61e883c6879f0e7806a427e84f609e60ef81d503a3098a12f025b8003,
0x108b2118004f0728000c151c2a40000b56c3b5942f28471d8c3b207650ecc1da43b5076707a6000e02e405c00b7016a02d039b800021ec43c887210e221d4dbf43d280060d5a1a9c351069a055611b4001046e0164152039b8000087d6ad876b2a5450723b187640eca1d98438c3d200070da41ba837206df0daa1b3c365032a,
0x10ef010e800084600e501e9c3a087400e7e1ce80e601ee034a07cc0f381db036e13e0284050e0a34151c2a4055b0ab80ff82a087100e181c28382800010eaecd5d9bbb5776876adac4d952d0f50002c144027c04a21168229843a000211182d0059f0b3c16742ce00830a8e15240005ab636fca26148d285e50b63b3c3d38001,
0x10b680001dad3b43b56c6dec7660ec61d943b20767152d0f5800182d705a70b4216702cc05950b2616482a407aa00016ad8db787ab001616f82de85bc0b7616e82dc85b80b6e16d82a48000b56c3b5c3d500070de61b4837506e40dbe1b5436786ca0654069c39e854c0a9a1cdc0003b948b804c49d9a92ff766f7348a9787a9,
0x10a88150c21001a303e407640da856603d4079400487ac000c145028d01b309f0076028401e40a1c14601f284e6030a072428183ca099c055c2a407aa0b5a16d03c4071b0e341c7038e87890e021c20387870c0e141c14388070e000021d5d9a865725ff6ad8a971b7e36f63b307630eca1d903b383d687a603dc079c3d505ad,
0x10acc07a80f280090a2814680d984f803b014200f2050e0392140c1e504ce02ae1e2038d871a0e381c743c487010e101c3038507050e201c380000875766a195c97f952e1dac6df8767952c0f5c15f0002800a008808a011a0055047208c4118004d0098007c20a841608441098213841f083c0fec000072a0e8419e833a0721,
0x1766a0888764952d0f601e9c0e601e703b606dc3d704f80a10143828183ca099c055c3d507080f101c303850705000021d5d9a865725ff6ad8a971b7e1d9e1ebc2be000500140110114023400aa08e411882300098007c20a841608441098213841f083c0fec000072a0e8419e4339866e0e4215102a18420034607c80ec81b5,
0x110ea195c97f952e1dac6df8765952c0f640014022001f082a0fec000072a0cec19c033386640cc419ac2a1842003b206d42b301e500121ec00d984f803b014200f2050e0392140c1e504ce02ae1e2038d871a0e381c743c487010e101c303850705000021d5d9a865725fe0888a970ed636fc3b243d8873f034a076c0003c16,
0x125fe0888a970ed636fc3b1c3da0740034a079c3d9050e0e18000043abb350cae4bfc111152e1dac6df876587b3000a0110026001f082a10781fd80000e5419dc338866c0cd019942a1842003b206d42b301e5001206cc27c01d80a10079028701c90a060f2826701570f101c6c38d071c0e3a1e2438087080e181c283828000,
0x10e381c743c487010e101c3038507050e20000043a865725fe54b876b1b7e1d9a54b03da83fb003e0000002872a0cea19bc33506660cc6198432f0543084006d42b301e500121ce80d984f803b014200f2050e0a000f14265014d0392140c1e504ce02ae1e2038d871a0e381c743c487010e101c1c386070a0e0a000043a8657,
0x10b52168c2a407aa00016ad87670ec81d943b187661b730f6e1d040d281f30f6a1468388000010eaecd432b92ff044454b876b1b7e1d9a1ed8002804400aa013000f8415084c10781fd80000e5419e0339066d0cd2150c21001f203b206d42b301e5001214680d984f803b014200f2050e0392140c1e504ce02ae1e2038d871a,
0x12a5c6df876907bc0f4c07b80f387aa0000ed69da1dab61d9c3b207650ec61d983b50769152d0f7600182d985ac0b4c15203d50000b56c3b387640eca1d8c3b30dbc87ba000c16c82d585a50a901ea80005ab61d9c3b207650ec61d986ddc3dc80060b6216a82d205480f540002d5b0ece1d903b287630ecc36ea1ee000305b0,
0x10a88150c21001a303e407640da856603d4079400487bb000c145028d01b309f0076028401e40a1c14601f284e6030a072428183ca099c055c2a405b500161ee83d5877a0f5a1edc3dc87b80f6c1ed03d987b10f54151c3d785490f101c6c38d071c0e3a1e2438087080e1e1c3038507050e201c380000875766a195c97fdab6,
0x10acc07a80f280090a2814680d984f803b014200f2050e0392140c1e504ce02ae1e2038d871a0e381c743c487010e101c3038507050e201c380000875766a195c97f952e1dac6df8769952c0f7a15f0002800a008808a011a0055047208c4118004d0098007c20a841608441098213841f083c0fec000072a0e8419e833a0721,
0x1087206940db87bd00de1ef0121800b0f741ee43dc07b70f5a1de83db07b40f661ec43d784f80a8e15243d507ab0e0a000043abb350cae4bfed5b152e36fc1ef82be000500140110114023400aa08e41188230009a0130012801f082a10582110426084e107c20f03fb00001ca83a1067b0e4215102a18420034607c80ec81b5,
0x1083e10781fd87420000068c0f901d9036a07a80f2872a0012145028d01b309f0076028401e40a1c072428183ca099c055c2a105430a881c843c4071b0e341c7038e87890e021c20386070a0e0a1c40387000010eaecd432b92ff2a5d6268a9607c0000210ac21c81a5036e017c03780007728ecd41110ed32a5a1efc000842c,
0x1508ea16c7630ec81d943b3133e00034c3a1f082be000500140110114023400a4015411c8231046001340260025003e105420b042208421098213841f083c0fec2a185440e420002c4d26424e0499f137f264a32bc00143e0857c000a002802202280468014802a8239046208c0026804c004a007c20a8416084410842130427,
0x104881f082a407aa0a861510390855c03dc1d000f385470000ed69da1dab636fe54b548d283950b6a26c7630ec81da43b3133e00030f861ca0041846208940a580008423088e014c1358005081415f0110000a002c005400a00120022004010081ff03fa07f00fd83ed07dc1d082a105430a881c842ae000004443b6076b1b7f,
0x125fe1f18394008308c011180000ed81daca11d42d8ec61d903b28766021f0f8a1f0414c829004fc119422f84530ab808381fe000036fea46948f28664cf8001532102210f8815c00050005044c010001d0039007000dc01b003504440884110021f043c103c2070409081409d0135844f0894022804187bb01261148000842c,
0x10518094c22d043a00021f143a087400f7e1ec039d01d3039807b80d281f303ce07ac0ed81b70f8015082ae07be0f541ea42a405470f461e880e485180a0c140c28003e507a00f281e284e609a41338265018502c4055c0a684f80a10143828a051a0e1e1c2438407070f101c40387070c0e141c1400008758b804c49d9a8657,
0x132ac6560cad195e32c032a86570cb0196432d865c267f0f9000003e207c30518094c3d387bb01261168229043a00021f143df873a0a841d043a0073f0f5415202a387a803a607300f701a503e6079c0f581db036e15a027c05080a1c145028d07100e1c1c303850705000021d5d9abb3776aeee5dda1952d0f8e00003e207c3,
0x11d906dcc3e587c8007400e401c0037006c00d411102210440087c10f040908140002c4d263f4cfe000c3e5000701da0458083810a019812483ca84ad093e129423d0002091c15302a687370000f05a3ef5cd2556eaad153d2b3a55044388fdd10f221e110183e48570001400141130040081e10382a185440e420002c4d0003,
0x10f9c0ba03e4844b01f4000424b843a00040b0023607cc0372077428401e80a1c07b028a01f40a341cf42a605580a8a13e028001a70e0e1c14388070e0e181c28000022283d2d50843ac7de3b3aecd4a97aab73f7443ca1d207cd000411b023d81a70372000021f3b94766b0e92202952f0f981edc2cf0000b56c3b307630eca,
0x103f60fb41f705430a881c840178030006200c80198034080a086010c821a043608702030000b134000d30fa61d0fa208e821407c10001626937f26424e049929345267c000a1f403e40225007e087010d8219043000c4018002f081e103820304050001626930f8cb6197099fc00187cf000210c0216000004450621a702839,
0x10b4816942d30000b56c3b44dbf41890fac0f4026b850606d007543c40709000054bc43a865972f47eed55b07d5001609a813485490f5616882d185a40b4a16980005ab61da26dfa0d587d407941344281835e039c1e2038400002a5e21d432cb93a3f76a9d83e9800208e011b0000043e6df90e9152a87d20af800140050010,
0x184d621d5dcb87d80012074c0e881cf0a0c0f4026b836809240ba0225800108a60bd424c05470f20179c2f485e30ab0155c2ae80f1036613e00ec050803c814381b884db07b0142438d871a0e381c743c487010e121e20385070c0e0a0000879b5424cfc54ba1359fbb10ea1965cbd043d0fae002c12182420a921eac2d105a3,
0x10a98156007883d00a0c1f602a385570aba1e20384800021e6d50933f152e84d67eec43a865972f41f68004016902d61c60000267e26244c1098612fe26144c00981130851344c19cbd87d90002112c22981d303b600240e881cf036613e00ec050803c8143838d871a0e381c743c487010e181c2838280000444d50933f152e,
0x10f101c28382800021ec7eec32c843d21c4439887410ea21d843c087908750fba00240e981d1039e07900ec01b30faa1418287050809f00010282836907a0135838d871a0e381c743c487010e121c3038507050e001e20000289a4cfc7eec32cb97a59a41f70000844f08960000111354283d4a26c3ed848d06d0000826b87d7,
0x109e200103ee80f101e003b807680ec01d603a42490002091c15302a685580a8a11403c4070a0e6e1c6c38d071c0e3a1e2438087090e081c0c38000005135101930e267e3f76196555b87df0766130827b834003721e2038280003f761964439952f556a1f7800380f40198125c23d03710680136c26103d80766142427c8737,
0x10434086410c0034006600c80188030005e101820285430a881c84000589a0006656930f87e2000a008c010002f006000c401900330068000065d32c7664a1f841ec050709b607741b887880e140000fdd865910e654bd59b87e007b0141c26d81dd06e2125c07a0007019811e83ef000903a606a40d181a20342068028204f4,
0x10caeb57897f1b7f26144c089823a070fca1e5400100070ea21bac37286e00dac1b4c368054c0a9a1cdc00010f2b9a4a95553a93123f751f79e0b10e226021f903cd00c0091211d805c80b8016e02d405980020fa411c816a02aa056c15302a68000b9a443c941c28585074a95553aaa573b3a1f8c00285790ae0002810e021b,
0x121d843c887410ee21e01fa80020700000021d043907e900061c5c00006560cb01fa03c805e90bce178c0005cd23b3843cc3f38007019803e823d0497000411ac3d2854c0a9a1cdc0005cd25568438959b2a5521d8439887210e821d443c83f3029f08d406641cb800809dc065c0cb01940c6c1c6038b000026184c40fdc8221,
0x159201fc01d2078800011f7163887ef07461e200002c708fba1fb800687190f081e840001fb43f6c7ea0fd81faa3f747eb8fdc1fb20fda002438087890e3a1c7038d071b000054a0a9315242a5854a8a91152e0fd8002038c000026144c18988130025fc4c30984130426244c0898707eb000e1cdc00010f621cc43a887110e4,
0x1000120f966987fb07a01e20000483f59a41fe81e5878800011ff964987f907941e2000047ff59241fe01e3078800011f7963987f7078a1e2000047df58e41fd81df8788000122f16a887f5077c1e2000048bd5aa01fd01d98788000120f166887f307641e20000483d59a01fc81d5878800011ff164887f107541e2000047fd,
0x109e41c0c00008738fb820182788703000021cdd9a080507d81e2000048ca5abe20101f507880001212966f880307d01e20000480a593e20081f2878800011fad63f080107c41e2000048c25aae20001f007880001210966b87ff07bc1e200004802592e1ff81ed078800011f8d63b07fd07b01e2000048be5aa61ff01e88788,
0x1000021cdd9b081109fa1c180000875782922f040804fc0e0c0000439c8bc101e13ec383000010e6f05040704f90e0a000241e8875101a13e03828000772a21d440604f70e0a0000439c83d772a202c27b070400011ff043abb54101413d4382000010e71ff040484f40e080000439bb54101013cc38180008fb821d5d9a0807,
0x110ea2070284070a0000f05c43a881b0a0e1c2800048bf10e6f05c40d05060e12000043ac83e772c20642828709000021ce41f08180a081c240000873772c205c2818708000021d5dab47fe102c1408384000010e71ff840a85010e100000439bb561028140038380008fbc21d5d9b081309fe1c1c00008738fbc204827f0707,
0x10a261c3800008737837230c41305120e1a00024218875104a14443868000773621d441205100e1a0000439bb9b9086208c287870c0001200c43a88220a1c1c300003b5b10ea2084286870c000021cddadc80310401430385800010eb1f89d9d081f0a161c2c00008738fc42078285070b000021cdd9d081d0a121c2800048bf,
0x10e2200024258875106214743888000774621d4418051c0e220000439c84b774620bc28d87100001202c43a882e0a341c400003b6310ea20b428c8710000021cddb1c80b10581460387800010eb1fa9da1082b0a2e1c3c00008738fd420a828b070f000021cdda108290a2a1c3800048c310ea20a028a070e0000f06c43a8827,
0x10c1e1c580001faf261620f0306871600007eac985883b0c141c580001fb1261220e8304871600007ebc98488390c0e1c580001fab261220e0302071600007ebc98388370c041c580001fab260e20d8300871600007ea498388350a421c4800048cb10ea20d029007120000f08c43a88330a3e1c4800008737847232c419051e,
0x126222120311071600007edc98788470c421c580001fb5261e2118310071600007ecc98788450c3e1c580001fb1261e211030f071600007ebc98788430c321c580001fb5261a210830c071600007ecc98688410c2e1c580001fb1261a210030b071600007ebc986883f0c221c580001fb3261620f8308071600007ec4985883d,
0x100007eec98988530c6c1c580001fb92626214831a871600007edc98988510c661c580001fb326262140316071600007ee4988884f0c561c580001fb726222138315071600007ed4988884d0c521c580001fb326222130314071600007ec4988884b0c4e1c580001faf26222128312871600007eac98888490c481c580001fa9,
0x110b819fc39b80003b396ad88718ec73b1a6dd442d867e0e6e0000ece5ab621c63b1cec69b7310b419f039b80003b396ad811090e31d8e7634db888590cae1cdc00021d426207672d5b152c3f70216032506fe0000875ca9788570c921bf800021d52a5e215832406fe0000874ca9788550c801bf800021d32a5a215031b8716,
0x100007672d5b10e31d8e7634dbe88620d0a1cdc0001d9cb56c6dec76390e33b262184342073700007672d5b1b7b1d8e438cec688600d061cdc0001d9cb56c6de476390e33b26217c341073700007672d5b1b791d8e438cec6885e0d021cdc0001d9cb56c10ecdbb8ec721c6764c42e86800e6e0000ece5ab636ee3b1c8719d8d,
0x1b56c6dfc76390e33b3221a4346073700007672d5b1d9536fe438c76388680d161cdc0001d9cb56c6dfc76390e33b26219c345073700007672d5b1b7f1d8e438cec888660d121cdc0001d9cb56c6dfc76390e33b1e2194344073700007672d5b1b7f1d8e438cec688640d0e1cdc0001d9cb56c438c7639d9336fa218c3430737,
0x136fe3b248729d9910e01a4c39b80003b396ad8dbf8ec921ca765443786920e6e0000ece5ab636fe3b248729d9310dc1a4439b80003b396ad8dbf8ec921ca764443686900e6e0000ece1d8f36ff6ad88728ec910d81a3c39b80003b396ad876490e310d61a3839b80003b396ad81109b7f1d8e438cecd886a0d1a1cdc0001d9c,
0x10e6e0002d5b1d9c1d9e439c43c069b0e6e0000ece5ab621ca3b3c43b869a0e6e0000ece5ab61d9e438c43b06990e6e0002d5b1d9c1d9a439c43a86980e6e0000ece5ab621ca3b3443a06970e6e0000ece5ab61d9a438c43986960e6e0000ece5ab621ca3b2c43906950e6e0000ece5ab61d96438c43886940e6e0000ece5ab6,
0x121ce2200351873700007672d5b10e51da221fc351073700007672d5b0ed121c621f8350873700000886d5b1b7f3b3676708758ecf10fa1a8039b80003b396ad8dbf90eb1d9e766443e069f0e6e0000ece5ab636fe43ac7679d9710f61a7839b80003b396ad8dbf90eb1d9e765443d069d0e6e0000ece5ab61d9e43a443c869c,
0x100007672d5b0ed321da2220355873700007672d5b0ed321d6221c355073700007672d5b0ed321d22218354873700016ad8ece0ed321ce2214354073700007672d5b0ed321ca2210353873700007672d5b0ed321c6220c353073700007672d5b10eb1da22208352873700007672d5b0ed121d22204352073700016ad8ece0ed1,
0x10e6e0000ece5ab60442766cdbf90f11daa2240359873700007672d5b10ef1daa223c359073700007672d5b10ed1daa2238358873700007672d5b10eb1daa2234358073700007672d5b10e91daa2230357873700016ad8ece10e71daa222c357073700007672d5b10e51daa2228356873700007672d5b10e31daa22243560737,
0x10cb254bcfddaa7b112e1d543c4000010e61964a979fbb550622583aa07880000a264a979fbb58e2b34043ab75c4cfa225439c8789000054a2d5b15242a445498ece152a262054b0fdc08940e5e1e20000131026241964fd588930e5c1e100001fba3f707ec898988920e541e2000006572a5c21d40018cba2a584bfc44886b4,
0x10000b1c5648acd04cfa7ee544c889d0f061e1000010f33f757348fd91fb811381df03c4800050707ee8a95130f2624767432bbb3510ea10ec44d87700f10000032b952f3f76a95044d076d0f10000043a9fbb21ed1700a97375c513299f421d88990eae1e20000087351327eeca97aab40cb2dd7133e88980eac1e200000873,
0x107e60fb800007d00e401d080f901e5035807d40f501d9036a068c3f6089e03522028418082d104e208440d880c0fd220242a105440e4206800d081a20001734887910e421d843a887410e221cd6269d9a952c8ff8227c3f301a703ba06e4406081b0001734887910e421d843a887410e221ccecd443a952f113c0cf83a50852,
0x152323b487680ed41d8c087c451874907ae077440d881c000021d6e691fba566e228824b837101f4136c3ee87fc1038000087b10f221d843a887410e221cc21d421e9fbb0cb222843d300b00126023c04d806f00ba0164234845208b210e421707aa00016ad941c289850bca469493284704422280005020503fe07f40fe01fb,
0x1114e001802e80590a901ea80005ab61da43b4076a0eca1d903b31a7008a6010c228c2258000b56ca26d48c8ed21da03b5010f88a50016093814e027c04ec0a201428251048010d4235045308b410e821785490f560002d5b263d5130a46942f29265070a16011088a4000c01c80450089011010f422585480f540002d5b289b,
0x10e4c1608113000a003c007400d801a0032006010382050408080c10103f207e61c8041981b31018076040d81e41042034c07280ed0a86151039085470a901ea82ab80000fa00c0825003dd10440af823d83b1101a0c5825703e7105c0c6825903e910620c2025303e1105015082af000010ea10f4a9721d721d6766d37f263d,
0x10442d400a969b7b1152003043e087b10f421f42a705c90b94172c2e605cd0ab00002d5b022121d676707679b7f115021f43d3800600d202c0047809b08d2114822c8439000222944468882110e0ba40fc81e7037e07300e981db036e20583f603c8037a06e8246081910200b701e703bc08121248241803505cc0b24002840f,
0x1034006840d108050352202006000f7000010f8a96087321d6766de0ba63c11581fa440d880803b606b8229843604f8093000588aa115215243d58000b56c0885a8035c036e06dc8dba1b7636fc54b445587e9104220380f381bf08b41108144025800000885ae0152d36f222a83f4880c101006dc0d7043a086c09441258000,
0x1658832d065b0cb8664a22c00050208040e081010103f6115c08c4118004c083e10781f781fe07e0000131e8cba32c46548002a61c196832d865c2642115e001400d0018001e004c0000cba658832d065b0cb8195ccb944570743037a06d40d18805101c0000439d89a4c7aee50a9588ad000411d824a01b003b81fb00d602b4,
0x1b56c3b387630ed41d943b2076634e111681da0049845308a410e83d50000b56c99f544c291a1d903b387630eca1d98088445987fe104013840f4037b09400c0c00008730cb254bc21e9d9d3f730f2c459036f05e8136c24c87fc03b8206800008730cb254bc21eb7de3b3a7ee5e0b88b1000a00880108020001e004c0000cba,
0x1016611b03e901ce0390069c3f601a9034a06880d081a01028204440408050a9815340005cd250710e921d343c62a5443c843988b601da12483d28002016611b03e9073d03aa069c3f601a9034a06880d081a01016205c4088808100a1fa4406854c0a9a0002e69283887491018a9510f2907a22d4003005f00bc15203d50000,
0x102ba051026884c906b80d28429084f0000a4616a8a85a4c7cb24c32c92fe26144c00986130226104c10fdc88b90fd6212841b88920fda000097f130a3f644c009861fa83f687ea8fd8130226104c109871fb63f707ee845c07e8099c13040ae813d0000b34131f2c934cfa4c3c45b879a01ca12242460002017202e005b80b5,
0x10cb221cca962ab5117a002839307250e481c8c2a207210001626933e195e32a8658137e88bc0b28002c003027404e2022c226044b0a9015243d507ab00fe0204041008301080214223026504cc099c134826a088e0002d5b021f50b699f944d88bb0fd403c4076800021ec438887710e421e0439887610e84cfcdd7c45d07eb,
0x1029013241a605420ac2000131f930f3f76196548c2d51566823003f601c1037e06a40d101a1034022f84070808100a000098786595230acd043988bf09821fcc09e880b0e8622b40de81ac034615844028808101c0000987865910e654ac45f080b115a1fcc0d604c20fd80d003ef01a00342068840281a910100002c4d1fbb,
0x109b6136826104c11006200840007fe0ff81fcc418882e1050208840e080d0a8415842a6856501a0034406900d301a80354000263f261e7eec32c843d6fba21d446088bc0444088420500000fa01c880c9818f030605f80b9813d09d813a827204e009b41304401880210001ff83fe07f3106220b84140822103820343f488bf,
0x1037e06a40d101a1034022f8408880e101020143f488c101a8034c06900d101a0120c001047f0a8415842a60565000098fc9879fbb0cb2a4622422b35118622f011102210e440002c4d267c4dfafe3c46108bc0e44088811080d708141fa800000fa018c1f4024b847a0326063c0c1817e06e205cc1a0013d09d813a827204e0,
0x1b13509a47640eca1d983b387680ed24df8231846202cb000098fc9879fbb0cb2767548c08c50fd806f40e081bf037407900ec01b302922040410881b1018131c3fa07e9118022fc4618000261e7eec32ca63f5231121046208bc0454083820b03fc00001028461072201ae03ec06707e6092e11e839e81b8034e1f8045e87ec,
0x10b6a09cc13502620486002c2a185480a921ea83d585570ac215302b28000261e7eec32c821f3b3a3b207650ecc1d9c3b407691b7036e46dd0dbb1b7836f40014dbf08c7000010242008035004e001433a866f0cd4199833186610cbc00182da800b04b615082a185480a921ea83d5855704a8095412b025704b00964000263f,
0x1101020143f4880d0fe610e02608253027a15842a6056500d2110c03c844600fe00009879fbb0cb2087cece9b7f1d8e99f44640002091c11e80ea88bd019c1fb00d481a5034406840d008b6117c205c40408050fd220343f984c1027a0fec00f80050cea19bc33506660cc6198432f02e805ba0b5015500060898111c222042c,
0x103aa1f8045e81fa0fd807180d481a20342068041908be102e204440408050fd220a020b0804100013bc272019a030610a8211023c046808a845e020e07f81c8846402e805a8112c221808600f215842a6054d0aca00009879fbb0cb2087cecea6fd000a6dfc76388c90e5a073845e87ec038c06a40d101a1034022f840a0811,
0x11d9c3b407691b7036e46dd0dbb1b7836f49bf400288cb0e860310067047608f402e800107d2091c06c00d381d5117a1fb00d481a5034406840d008b6117c205c40408050ac215302b28000261e7eec32ca6fd50710e921e243a6878d101843988ca0f3403b8076812001f603e807a00cc0912124825a049708f4000824701c8,
0x10e421584000263f261e7eec32c821f3b3a23303e80193031e060c0bf0173027a13b027504e409c013682608803100420003ff07fc0fe620c441708281044207040687e911940ba016e82d4056c0aa82258446088610c8215808d010a01f80340060000c232446385480f54155c2b08000261e7eec32c821f3b3a3b207650ecc,
0x103981ce82a385480f54204440a082910161fa44068000b56c087c7650ec81d9920f4a9688ce0014085010802220442088010f821e080010282a20721000098fec4d26fd000623340050214042008881108220043e0878200040a0000232c463025904b0095c12b025504a801dc03b007500e801cc039043e087a23142a10544,
0x13b287658ecd10f111a20018042807f0a901ea80005ab61da03b387650ec81d983b49a8188d00fcc032c06500c90190031c44c073d034e1f8009f07ec112822f446701a9034406840d0080b117c204440408050fd220343f984c1027a155c2b0854c0fce15943c100003f704c3c32c821f3b383b287640ecc4cfa233c3e281ee,
0x1b1357348ece0ed01d9c3b287640ecc1da432a86570cb0196432d865c1d8c3b1c7640ec91d943b2c766887188d40004127c23f010601a2000021f2a7a566a439c469847e01aa00083f507dd0a9815342b280003f7619648790875566a43c087210ec21d043a887110e611a400302f105db0a9c0002e691d9c3b187638ec81d92,
0x10cb2087c7680ece1d943b207660ed211b0000824f847e020e0350000043e54f4acd487688d7000412b423f011601a4000021f2a82566a43a446b049805e20008006047e0b92034c2a6054e00017348ece2b363b187638ec81d923b287658ecd2b3521d62354002866a0cbc21a4003000c111216fc2a185480f54155c2a70000,
0x1058a0b1016182c2037e231021f08c6007400e401c0037006c00d4466840900001f400c9818f0720060c0bf037d06e205cc27604ea09d6139027004e109b61368401880210001ff83fe0831105c20a0411081c0fd220500e6085802be0f1c22308d002bc15082ab85610a9815343f38565119e23303c100004c7f1ffcfdc130f,
0x1105c20a0411081c0fd220500df81cc10b00b1c16302c505880b0c161015f078e2310223043d110e221844208851110220c042007711b0233c0af05420aae15843f388cc0aca1e08000263f8ffe7ee09878659043e3b407670eca1d903b3046c847e01a0000846907dd11ae235846a88d411a6234446007f410200b2416382c6,
0x11050208840e080d0fd220500df81cc10b00b1c16302c505880b0c161015f078e2310223043d10ea21cc43a008200e805782a105570ac215303f388cc0aca1e08000263f8ffe7ee09878659043e3b3446d08cd0592000046887d011a4064c0c7818302fc05cc46004ec09d4139027004da0fe8200c40108000ffc1ff04080831,
0x136f46dc8dba1b7036f86de076788dc118c01dc03b007500e601c821f043d11b415843fc84d002bc000131f930f0cb29bf148c9fb8043e236c46908d511a20b2446680000fa0235c46b0193031e0e400c1817e06fa0dc40b9813d118013b027504eb09c8138027084db09b413043fa0803100420003ff07fc0fe62040418882e,
0x109d4139027004da09820d300010803100420003ff01e40ff807603f981b311a422844188830105c20b441408241044208440e081b101a20302a105470a901ea82a600df0fd415342ac05570ac2000131f930f0cb27eec87910e421d843a087510e221cc43c043a88dd04b6002c22105a000ea15243d58000b56c9bf148c8221,
0x11da054b533f0ed236f83b1846f00060126237014c00ad04f809d804780ae05340288146825100de1194232045308a41198233845c08ba10e821c800111b60d2c0fb01f303d2076c0db81bf0e741fb040981c1037a06e83fb0810099a1fd00aa84c90fc4052011008cd081400003e803550326063c0c1817e02e604f424284ec,
0x1003400141fb05810af808142a1804e00a00002c4d0005195432e131e8cac6654656c470025b088422ac2d585aa0b5216a003b80670aae1504202000052329bf0110952d1da6237c40b81d30fd21f6c40d827403b6002c22905b401260234003077a0f721ee83dc07b70a8e15202a487aa0f560002d5b02211d943b207660ece,
0x136fd07ac76788e410a61f643f6816802c40d981b18146028a05100a1814202820d201a3034506880d081a084d209a6131026287f4101e1fe840c00004df899f944d08730cae238c3f404e0098805f80a400004c869bf16a8ac96261e23880ff800a07e215dc00905440e420002c4d000532c09874caa195632bc656865888e1,
0x10f54155c013802e000162699d21b7e1d8e239c4680064089410d8133824900162370121823f047a15243d585570a82101000026fc50b2a46542d8eca36fc3b201108ed236e46de07681b7a831223983bc824200021f38215805a0a8e1eac0005ab65072a164dbf0ec911ca22ac2ce807500ca09bc1380000b56c54b41109b72,
0x111d00278144028508b211683a0054711ca155c2a0840400009bf0a96a85e5072a16548ca85b36fc3b1811088e91156167c2ce807500ca0018030077e0f9c090047305470a901ea83d588e50aae150420208df00009bf0a96a83950b2a46542d8eca36fc3b181109b7236f03b40dbd08e8000a1978335066f0ccc198c3308543,
0x105120a1c14302840a8e15243d58000b56c6df876328595232a26c7640221835e23b0000845a087c0a3012d85470aae150420200004df8990d42f291936fe23ac03a07c5087a000447488e711ca15203d507400a8e155c2a0840400009bf0a96a85e5072a16548ca85b508ece90dbf08ea1168019047207ce115216d01390242,
0x111ce150420200004df821cd9d21b7e2a5a23bc124877d086c22a42cb006311da028004e809c08b623b046f87ab11ca155c2a0840400009bf0dbf0ec62a5aa0e542ca9195136a17c11088ee0fac1f3800308b40a8e15203d50000b56c6df876328391d903b487660ece1da83b28476808a0fb61ee8138800b0f961df83be828a,
0x100161f382d688b411da151c2a487ab0f961ee83dc077a0f541ee40005ab636fc3b1941c8ec81d943b307670ed411e222d0030007500e801cc215843d00016ad876328391d90a46410f88f0116801f803a807400e610ac221843d000223b847508e503dc074c0e601c6037e06b80d285470aae2014404080e1022205040b8829,
0x10b3616682cc806400b8151c2a487ab00016ad8dbf283950b2088476688f400160960126024b088410d82d0059f0b3a01d403288f20f9615243d5800111e023942a38000b56c6df8763283950b2a4647650ecc11e6002c2da85b411e21ee43bd07b80f7415243d507ab0f960002d5b1b7e1d8ca0e47640eca1d983b384790243,
0x111ec0002d5b1b7e1d8ca0e542c9b7711ee0924005843604860908120823f00021f3821585970b2c018c02d85470a921eac0005ab636fca0e542c8ecb11ec002c12482430484090411f84360f9c165c2cb006300b623cc47a000111e0151c2a487ab11ca0002d5b1b7e1d8ca0e542ca91911ea002c12482430484090421b07ce,
0x10906000823f82e8059622500bf845a0fb60a20138800b049610d82cf859d0114019412d08f20f96110447a05470a921eac2a6054d0ab0075440b81c10fd806a440401bd034006840d10805101c239447a88f611ee155c2a0840400009bf04399fb8727c6df8763152c5072a16411088f811e800043dc84330b4009242a388e5,
0x10aae150420200004df8a95559aaa57087623ec2d0000b11e4090c1210241047e08f811e805c00b410b021585490f560002d5b1b7e1d8ca0e4765021f11f423c8032805c086410ac00088f811ec23942a385570a82101000026fc10e67ee1c9f1b7e1d8c54b141ca85911f21fa807800e901ae035406a00d301a403440680492,
0x1097c04c419787eb11701e0839b000059227ee098806593f747ea8fd81fb626044c209891fb226144c1098612fe260023f43f5814d0262049409184cd097c1e18420883e06a20cb819207ee100c1fc040487f61024000043993100cb24c38981130826247ecc47e079a01ae034c05c80b8016e02d4059848508fc11ac2a68558,
0x103d0079441007fe09c20de84070811102e20740d001a1034420140d488080a8e15243d585570ac40000439865954f67edd321890000b423c0215800108b40a3047a854700016ad9321a83950b2a46542f0ec611fe1fb41968325097c1e1809701230fdc20183f80809000021ccfdc06593f747ea8fd81fb63f507ec898088fe,
0x1050809cc138827004de09b822d87db00020264043076611ea23940f301ee03a607300e301bf035c06944028808101c204440a08171052151c2a405490f560000439dab64c84ed6cdbf152d1202002c13f82610518115c222845a04e609c4138026f04dc00043ed84430128021803c88ff03ce07840e981c6037e06b80d287ec,
0x1083c0002c4d263d4c7e9bf4002a6424cf824143f500d201a2034024182cb11ea0aa83e90903056c11d848100020ea215302a6855800016ad887910ec21dc43c152aaa75566a6df8ece90ea1d8c438848207a50166000087b10f221d44389b7e89030fd402fc05f00bd000043d887910ec21dc43c087510e26e3a24080058289,
0x108d201740005ab636fc088613535c21d8ca498eceab3554c643c821eb4e021c8439887410ec21dc43c0dbb0eca120e15f000500050476015c0220228085410a420a8416053e09f82a185440e420002c4d195e000a32a865c1960195c32d0cab195c196d09aa13b1b7f120c00e820608af004a23083a183fb0a861510390804d,
0x14c7a2428005057c0af615e42a2072100016268caf196032ac65706598909001408140fe83f607e215c000c00100a881c84000589a4c3a6578002996032ac657131e8cad1210034c24187ea0596043422104aa00ec0c4445304620b5a0a5012c800b0e501ee83e585480a921ea83d5854d0ab009d813e008f01260a7023500b0,
0x10288050c0a1014106980d1826204c50a9a1fd040807e9101c070406780d6020c041c423884e10a20002e69152f21d410ed59a37dc6e447edcfdc065712181fa44070821038207a024184a000010f2e242152f6fb810f448588e011c215d402780051210150c4848000b1349874caf0005195432d865c0cb4195c6580cab195c,
0x102720e4c1c9038d09d4139427004e109b6136826104c109da13ac3f4090c0a9a1fcc40687fc10381ff8411080010502008417080310621fd040807e9101c070406780d6020e211c42708510a8415880005cd22a5e43a821dab346fb8dc88fdb9fb8121a1fa836906e40d941fac09484b60fdc201c0d3846b120622700a30145,
0x13f551a8448788070f8c1fb83f584b7109a210819287820fda05300a301450288050c0a1014106980d181a2834406840d0426204c50000acd043aad513f6c7ee032b890e097c1fc0198080a0e4006c045e0471042a240820007220dd022701a4034c099200000a201310fa01fac0c6038202f805ec1bd036d02e205bc19e013a,
0x10f20179c2f182a6120611b0235854d0374033c0005cd2782a5498a9415242a5cecd152a90ea6fb810ec48907eb109420dc0001312261c4c08984130a26084c3097f13003f5e244445c078200007ed8fdc1fb03f647ed097f130a26004c30fd41faa26044c209821fba12201fb41a603440000acd0fdb1fb83f607ec8fda1fa8,
0x103c820840cf82c10001734843abb34782a54b9b7ec4843b2c43cc48a07ec037e06f416600d80f20179c4508116020e041815d82c1095a127c23d848200042448067854c0a9a15940d9880c03b0206c0f20821037407041a004c20fe620340001fbb54f4aa0959a065910eaf055d9a2a5521d4df7048987ec034c06f415500d8,
0x10ff022f040b02150394100046680000fa01c882a101f503e407a80f281d9036a06f42b307ec037e1ea82a382aa05981580413882d106006cc40607f3101a076040d87fc1038079041087fe104420084170000262421d4a912d50782a54ba1d2c4848bc5188a2e71d9d122a1fb00df81a4059802e83c805e7036620300ec081b,
0x105440a8c15282a6054e0000ecf08757668f05421dc3a53b14438cece152b122c1e983d3806f00f001c412e04390880110400088bb0e821cfc3a0018b02d6057c0c8017502fe13a026b87290fd620043fd015a029206300be017b02e205bc09d01391056206426884c709d4138026d04c103da07443f40424081e133c11c0227,
0x110200ca40001fbb566821d5d9a48bc8b8243a9bee89170016196832e065b1178001410a86630ccc19a8330865e0cea19bc200086710c6218442f885d000c0000006087110fc21ac4398876110622243d587aa0a9215203e807220550155c2a1854203ea07c80f501e503b206d40de81a40acc203040d8821104e20b441802a1,
0x1000c2340453032710e221f8435887310ec220c44487aa0a90151c0df81a60ad01fb048b091507140da01af0355094e12342450485021a03a4071079a1206245016082a601721200236046b0004120406a80d401a40340429854c0a9a15382b281b310181fcc40681d810361ff040e01e410421ff84110802105c067c3fa81c1,
0x1031805f00bd817102de04e809c84c809a2131c27504e009b413043f404cf0fe620343fe081c0ffc2088401082e0ff0000043aad5052324c487640eca1d983b40767021f8fff178848c08d902ba1fac0ad014b031805f00bd817102de04e809c84d1098e13a827004da09821fe03f40816099607303fb04461026000439d042e,
0x10b9a0394489848106bc0d341be839012200d6c2a707a2033e0b0416402a105440a8c15282a606ae0d641ad04e1071813ac09c813a09821fcc406816f02e213681b504db0ff820700bd817c09c01ff8411018c09d42008417000010eaecd1e0a843d54aa767224243a58bc67ee032cc6a04c7c246446c815d0fd60d2c0ad014b,
0x184d23b4931f9d943b2c7630ec71d903b247672242091d1226245c408039009d62008417037d09c21ff8411034d09901fd4195000010eaecd245e06593f76a954875091c0a82231820200001d903b287660ece1da109a4769263f4df8246c46302ca0abc00007640eca1d983b3876842691da498fe2421d9b12340b70006048c,
0x1093e125c25a04b2096212b8256854d12360002e690ec81d943b307670ed084d23b4942d263f5504ab095a12b3654f4aad159a2a77087a247c48e82dd091817342e605cb0b9403942a70000b9a43b207650ecc1d9c3b421348ed250b498fd53b843d3b28765a24210eb123c003048d02c805820000ecf0ec81d943b307670ed0,
0x10ab81eac2a301b31018076040d81e41042000010f9b7036e46dd0dbb1b7836f46e0043a95222a5ced56c4d89210fd4173c2e0800c05b20b5c07380e601c8038c071048b091415342a707e7000173488751d8a3b307670ecd1d963b28764153b843b12401fa848f010601b0120806300f402420c6408f031402300458240847a,
0x184d2087c43aab342a5d62690e929198ffe54a8dbf47dd907eb1cd63b90ea4c7f1210491874504341070204017902aa137026507e8119e19581a4834b0a881c84039007300e810f40000ed6043f62690e929192a546df9639ac77658ccb28cb026fd000a99f4cab195832b47670ecd10f28d40248821981ae04981fb00058566,
0x107ce0ec41e703c807420f743a488a2069824883f3891a059815302a68558101a2088417083110681118468002f008c197448d83fb003e087810f8220081800002048542006a001433a866f0cbc198c33506610ccc00182da800b04b01eac12c825504a8095812b807300e801d803a807200ee10f42a407aa0a8c09742a18000,
0x11026071822202620ff420640e9844c04e61ff440f81e108ac0a0400f8035000a19d4337865e0cc619a83308666000c16d400582580f56096412a825404ac095c039807400ec01d40390077087a06fc2a407aa0a8c09742a1800084d2087c43aab34782b6268a96952a36fc43a931f8924120603a4235848d0004247c1f583e9,
0x102cc04c415f07eb0cac0d0009c88d90984130409601290250049c092812402461fa03c304b706920d2c194834c10a61d241d080d81224035806784800004120849183fb0000102448d854c0a9a15600d9880c0fe620340ec081b03c820840e0854210a820580e6044611a01fb840381a50858090c3f8080a035c10cc12607f6,
0x1124e003016e02dd05b60b5816102c305880b1416302c70000767942d263e890b0f1c49307eb02ba057c0b88139028c05140a201430284050426884da098213243f40918099e01c8039807400ea01d821e87fc10381fe0000021f5232b34142d08758ffe98f898946a08bc424940770902091a11c41b403340198135c25f0479,
0x1099a1fa03fb04ce1026057c0ab01c410b01f881e387f8000020583e80725039407d40f901ea03ca07640da81bd0fd80760418082d104e208440d880c0aae150420681ba037606f0000263e50b4767141d3c152a5c54b22e11fb810ea24a0492835e0698214c3a483c80001734810fab342a5ca465668285a10eb1ffd31f2a76,
0x1000c4c49cbc39fa727ce7f9ca3398673f23b207650ecc513624ac45e0227042a103c20000000e441f400a40193031e060c0bf0173027a1fac3ec816b0a8204e409d016f02e205ec0be018c02880000003131272f0e7e9c9f39fe728ce619cfca89a72f624a83f601ca0344205040280004c7c5488a9215262a5c54b04398929,
0x100e410f821e85430a9015243d507ab0aae150400000064df899fd48c821f125822f01138215081e100000007220fa005200c9818f030605f80b9813d0fd609d00a5000b087a16b403b80060ef409cc138827004de09b8046808b01140218226044b0a9015243d507ab0aae150409c813a02de05c40bd817c03180510000021f,
0x1050a02c4058029d0538114822984390874116422d046908d4066c0bf8175027e13bc27004da098220103ff07fc0fe620d0411081c101a15203d50000b56c9bf032c93115232088443a892d081c00ec0000005080219a8330865e0cea19bc331866611ce00182da800b04b6096412c025704ac095412a007700ec01d403a0073,
0x108ca116422d045208a610e42270001125c1d043a001a50f601efc2a385480f54155c2a08404036e20300ed881b03ce20840f9882d00009bf043aa89a2a5aa465d9a892f0016090c12d825904b0095c12b025504a810b021f05490f56155c2a0840400009bf148ca839043e24b800308dc011e09d8037806904a2027804d8288,
0x1034c24bc0f9882d03ce076c2a38557037e1fb00de81ba03820d340f20821036620300ec081b0a82101000026fc10eaa268fddc6a0782a4c4449888a60158027804d8093010e10b846f846408b2114822685570a82101000026fc513454b548ca91a50bca19941c02211260001846e0297013c0a20142809304f801a4139026d,
0x10fdc201c496027c010c0d6c49288160398214c22308d00fe6203448d87f0101406b8219824c0fec204c0e3044404c41ff440f81e108ac0a0420c0046000a197833786750cc619a833086660a86000020088e7000c16d4005825704b01eac12c825504a809582a487aa00e601d003b007500e401dc21e854804b610f80008930,
0x110ea4c48a971b7e1d8eb24c98839f912661fac0b8813909b413043f9880d0ff82070000087526244c40980130226084c18984130a261c19644990919055200083ef849b0fc60be817302c906ec0d5419a065606d0137826684be0fb4135c19487e80f0c0520269017a02ac04dc096014b02d615302ac085406961fe840c81d3,
0x10198035806782c10962127c24b847b08f41204241054d0001734959a267e5568acd953d2a82558443c955baa753b3810f449a87d9024e048c0ad815a02b2056026904b6099c000144d131259a6b1c533f2c9325fc4c3032b89340fd605703da04ce0fd024c80a40146028a05100a181420282151c3d505570a82101000026fc,
0x17668b34d33f426b6a84a9dd648ac730006cc94cb012fe2618987832cc8bc260c24e016609350904000849b054c0a9a0002e692b34523299f955a2b3654f4aa0956110f2556ea95d53a8937017a22e807000df01bc037006d80d908e21234242800021ec99f955baa5754ea10ec49b049205cc22e83b2811c020e041807a02bb,
0x100140814102020304040fcc09a84be066824dc1aa820e06d013341fd07da09ae055409e87d90fd61510390854c0a9c15602ab88530fdc201c09d04c1068013083f9880d02de13681b884db0ff820701be84e102f605f027007fe10440e40275818c09d42008417039609da200c4188000b13421d544d1fbb56684c40a972919,
0x103a606fc42a07ec038224c41a685430a8e15202a487aa0f5615302ac05570a82101041681b310181fcc40681d810361ff040e01e410421ff84110802105c200c41881ba037a214c00026fc10eaf05544d1fbb8d4024e423d82bb0004003024505ca01ca2470194878605cc0ba017282e305c40b8417002de02541f7c1f701ff,
0x1028e050032e802f003e00003fb07f006b624cc00284011026202849289270ff019a8330865e0cea19bc331866611ce02180e301ae102c00182220433039816d413e02620498111800588d01236096c12c825804ae095812a825400ee01d803a807400e601c8496043e087a000449807ee0ff406984038819125e07cc0f381db,
0x1095a12b824f84a0092e126023d847a07200df41b8834009d6138426d84c210041ff83fe07f3105c208840e080d0a9a15380005cd23f7699f944d2ab7087a196443a893a126a0008166048b05920b7032b036806681f6826b8155097c05980a8813112701fd01cb039006fa0dc41a004c909da13ac27084db09841fa049a0405,
0x103ba151c429827c010c00182da87aa00e601d003b007500e401dc21e854810361ff040e07e911c61130139800b04ae09603d5825904aa095012b025b087c15242ab85410808000137e1fbb523299f810f9fb80cae767159b893b00180b9817402e2092422e808b0312020e041818002fe01f403d017882eb05760ae006600c6,
0x1556e10f4ece2ab45504acd849e800c05cc17342e584920fd422e82a6854e0fce0318066047a05700aec23d8312062812b808b0118095a0bac178849801e803e824b8000b9a499f955b843d3b38aad15412b3621cc24f03f70807096c24bc09408580fb205ac0b3816602ca059026903cd0ff405c40b7881909b21ed03ec0371,
0x10864023c03100000444a46942c8ec91282000422c84320136018c000022250b2a17876589400002119021900ac00c80000111285950cc3b3449f87ea0bb817282e185c10a9a0318066011602300002e6910f26eb8dca8ec6893e00180b9817104920b8803ac49e02f105d612602a702b8057611ec1890314095c0002e69267e,
0x15234a26142f1d9c3b3243c07660eca1d90a16c4a2894211182218440887900016ad944c1d9c1d983b28764285b21d225103d3887c12842234441088700016ad948d289850bc7670ecc8ecc1d943b2142d90eb128610e40008069088c001846805470a901ea80005ab651303b307650ec850b63b487680ed41d9c25080008452,
0x10ff020580e609451282250049f82db11a2003017481f303ce06dc0d701db03a615342a7056505be0b9017502ec05da0bb8177854701780304406081b104220b40001fbb087b101887210ee21e4766a243dab66e38195c43abb55772e54b44a309421100221444588780fd425104a180bc0182000087b10e421dc43cad5b371c,
0x10084010001f803e007a00ec1f9040e00001f402a18542035807d40f901ea03ca07640da85660fd825180d481e403ba07600d98819101420c041688271042206c40607e910121fe83f804d3097803a807780f209200b9c2488369066811d00001fbb087a99fe3112b37890f6ad953a0657128e1fa807280e401c612301af04cf,
0x14c4665800029954195c6558658195832b465704a507450440086820e040c0810011801a802f000098fd30fa62332c46548cb0000532ac65606558949006a001420605870440242400502000e8c08c4026841f083c150c2a20721000098fec4d263d4c3a988ccb0000532a832b065c0cae32ac32c0cac26421290001400e8018,
0x105be0b9017382ea05d80bb417702ef101c204440e81a00342068840281a9101005880b380003f7610f533fc406890e1964439952e782ce5ec980130226084c18985130c2a582530011800507fa16202c1020d0a860002c4d267d000a32b065c0cae196032a8cae894b00941d1820e02000e8a00282a207210001626931ea61d,
0x1036c202c000065910e654b4988bb95129a00142c385810af825284a589490476015c1198051085410a4211042103f007a841908261008200027804e507300e1425a84a6063a0c1c0060045008808a01748415082c05ac00007430e401fac3e507210a88150c2a101df038806f40d181ac117c07642b307ec1252214c2a70565,
0x1101c073040a00003f76439087710f2b56cdc7032c88732a5aa4687641d9c3b3243c159aa91e524cee504a787fe09c020800bf81e7128a02c0051846908bc0004478073a036e25342a38811034a20140df880e0398205000010f621c843b88795ab66e381964439952d52343b20ece1d9921e0a4794931311129c130409f87f3,
0x108b610ec000828b04a41d98480817e09c01ff841001e60a8e15203d501c61022073040a01ee10520002d5b065910e654b4764130f513299f1dad8950128421f044107ea11a60df427087fe1040079c4a289440160028c049846908bc114800088f511e01ce83df81b70a9815342b285470178030440881ae1010069440281bf,
0x10a84000133fdab65136a46941da85b523ca49933e285eb13498f476389530f7601b4049843b08a4094800088f511e025000f3854700016ad9da1952d5234a16476428395232a26533e3b5a1da43b3076309520fd4221c4430885000043d887210ee21e56ad887110ec3b3843c07698951000c027c04c807000dc01b4036006b,
0x108d202c0000895211e0151c0005ab6768654b548d28591d90a0e548ca926513299f1dad0ed21d8c25504830231009a08cc0288045041c009400f841f083c1088210841507f80fec00007ca0e4009ac146029004fc002c13082760894111422d046a08be114c139827104e009bc13700010fb6110c043007f00f2151c2a487ab,
0x10f6006b80ed81d31298059c0b10134026604c4098012f025c135c25f07fa0fe020683f008291030205c40a0811101c202440408050fd220703fe04db0fd0251c06080bc08e80cd0429854d0a9c159407500ef01e4124016f82e405ce12441b4837105d40bb017682ee05de151c0001fbb087a99fe3112b37890f6ad953a0955,
0x100fe021802f005f00c0016423b02b309040b201c284a6060e0000fdd843d4cff1888ec55ab654ea3b1ca96a91a3b38766487810ea772a25582b08953026a25504a881e712a004f426087f3036c202c4a787eb129c07e40f58832104c201040004f009ca0e601c284b5094c120818e83070590234400602e9039807180df81a5,
0x112041dd42a101eb04d609f8434855c104c002c09d016802ce05980b2816402c4200013082760982135c4a684e50894111422987e804e609c4138026f04dc000426987db114a1fcc3fd01d3039807180df87ee1016206040b88141022203840307e91018214c2a6054d0aca03bc079049005c80b9c24883690a8e15243d58079,
0x105dc0bbc2a380003f7610f533fc6228d47121ed5b2a751d8e54b44ac04d30fd01fe826d88190ff8074c40e044b0fd2000440884390e7406dc03480860001188a35182221d8e54b5dca09570f8823ac0f988bc03ce20b03a10820100404a809e87fe09d61fac115022809c20e40091841606fa12b43c3000011ae046019487ca,
0x15072a26c4ad013f0e5813041d787f3101622b43f401ac0acc134c3f607fa03aa06a40d101a10340206040b8808100a00023112ab63b18763ad5b152c5132a0e4fdc43a4876421cc4ac81db103425583fe075a09b60c043f408d10018134c17487fa03a6206040b87e91018255c2a7056505be0b90173849106d20ba817602ed,
0x103b206d42b307ec039e20643fd04d30fd0136c0f207fc03ba07600d98830105a209c410881c10362030000267f8c44acde3518ed61d8e54b0dbf087512b613643f4017509b61cb03fe03af103820343f4895906200a9c00602e906ce0b7c17202ea05d80bb417702ef0000767a3112ab6880c766a351c487b56c54b148da899,
0x1102e204840408050fd2256c2228262001609d4136844e12b409ec13d027904f009dc22a042e08720004228854e0aca0b9c24883690a8e15243d507ab00b201a403c808e12b025541b880003f7610f533fc622566f121ed5b0ec752362570207003b000000143e8066a0cc2197833a866f0cc619982a1854203ea07c80f501e5,
0x1129805d009d085809820f5040d07f302d005980b281640ff8202c26b84db115a1fa00d6056609a61fb03fd01d5035206880d081a01030205c404080509220da41b702f400007eec21ea67f8c451a8e243dab62a58a468439895d10b00b0019f016b08f60cfc26b88bd0fd0159826987ec0ff407541e101a9034406840d00818,
0x1096e134c06f03290fd024083ba854209b621a42ae01e40ff807740ec01b312b620c041688271042207040d880c0fd225743ad048208ec0c0416902c80566234400602f412b825602a6854e0aca03bc079049005be0b90173849106d20dc417502ec05da0bb817787aa12aa0000fdd843d4cff188959bc487b56c3b1c4af016f,
0x109b2134c3f404db03c81ff00ee81d8036620c041688271042207040d880c10a615342a7056501d403bc079049005be0b90173849106d20dc417502ec05da0bb817780003f7610f533fc622566f121d53a952c10ea257c00007d00fa207d40f901ea03ca07640da81c40346204c3f607f6039e132c403881906aa1fb83fd0489,
0x10460107c000263fb134987531ea623000a6580caa0cac1970990932509600f34037805f875a091211d818082d20566234400602f402ea1fac0a903550994132c3fb015d02b605680ac8158102613380e207f80fc4205811281ca1122103c3e500000fa0150c2a101f503e407a80f281d9036a15983f601cf103205c40b787fa,
0x1004a00701f8800f0aec008800d00120001626930ea63d000a658065c0cae1962258c4850200004a0fc40110012129025241188230009a013020f841e0a881c84000263fb134987531ea61f4c460014cb01954195832e0cac264212c41f8420403fd0432082c000261f197499f4002995912c2252002a8239084c109c026041e,
0x1035206880d081a0103a206040b8811101c202040287e912be0da41b880003f7610f533fc622566f121d53a952c12cc1f8420403fd04300828000261f197499f4002995712ca00142c385810af825284a589490a881c844b0854312c61d10000263fb134987531ea61f4c4699f40029954195832e0657195612c8242810001ff,
0x103e620b40001fbb21dc43cad5b0ec62a5a3b2043a9d9c21e0195db8eab3521d44c244b401ac115a2020000589a2a56ee5043989670014081410001ff07ec0fc400c801112c825944b08045008808a020a841603b220683fe07440000136c3a187ca0e4215102a185420fd0077c0e201bd0358068c2b304d30fd824a43fd01d5,
0x109220da417502ec05da0bb8177854700007eec21ec62221e4766a351c487b56ca9d4763152d1d9021d44b5000610e221f84398876110622242a407aa00016ad87630ec83b38438c4b487bb10ec22243a0874012041efc0d2882b11ae201c400837d0fdc139826f84b6030e05f0093854c0a9a15942a3880c03ce20843ff0822,
0x109ce132c403838a06aa1fb82550489096e2238444011001bc0ca4481077512d225a00ca818003a613b8271881907300e140b8816f0ff412d4253075a090411d826c84d3063a0c40183830105a40b2015987e811a2003026d82f4100807cc40001e70ff8076c41a082d1050208440e081b10a615342a7056501de124016f82e4,
0x136fe088432c92fe26044c10983130826184c00985267d12d800003e207c300016ad8763152d1d90ed0d41ca85b51366dfc1108ed25234a479dad0ecc50cc9908003267c12d61fac0ad015b0f8c0574136015f089222ac26700010ff0112c40b01cd0b40167c2ce808a00ea01943e387cb0f7620ac40987410e8020043fb01a5,
0x111e023d41e707fa03a607540e601bf035c1fb80d288291030205c40a080e1010201840287e912d4214c2a6054d0a9c1594077849005be0b90248836905d40bb017682ee05de151c0001fbb087b18888791d9a8d47121ed5b2a751d8c54b4764096d027a13043f587f3129a1d340db843a04a6201800013122a5a21cca9721d6,
0x1523425b84b5841712d823fc0f980b003ce20b02348820100407e40f587fe09d609f8419082609c20e40094012308a62010400037d095a1e180ed84f009ca235c4440118065220681cc038512041dd40b4016702cc05940b201620ff812d4253075a090411d826b84db063a0c1c18082c805661fa04b488d10018000426982e9,
0x1034206804040805000054a0a97152c2a5421cc4b807e809b6134c3fe07fa103420603f4881b0001188a351bc1712de1fa026d84b70fdc1ff0194880710381dd43f4848210100b203d801ae10d6234400601da12820bd02a7056505d40bb017682ee05de151c0001fbb087a43b88791d8c3b2c766a351c487b56ca9d4a968ec9,
0x112dc25784aa81db0ad025c407780f209200b7c17202e709220da44b7837100007eec21ea67f8c44acde2438972101406a43f807ec0ede20083ff01e40ff81fcc0d9882e1044208440e080d10181fa44b803fe0acc150421e05570a8a255419a096610a607600ee896f06e20000fdd843d4cff188959bc4872a5825c43f601a9,
0x1000223d44780547000099fed5b289a5072a46542c8ec81d8c25d800285840ae0150c000589a195432b86580cb2196832e0caa897503f600281f70742000099f0003196232a4000ccab195832b46570cb0261d12e8134c3fd07e8103222843f488170a9a159407980f501ec03dc07c00003f7610f631110f26fbeee584b9896d,
0x10fd0201040007fc0366228441a0830105a20a041388211038203042981d803ba25bc1b882f5070a12940858398096804842a387aa0ac0073c0e801d312e60ba446882e40bc00b9c2ef05df05be17743f500f601ea03cc07780f801e403dc24c897201d412402a6856509220da40001fbb087a99fe3112b3710ea25dc2270275,
0x1125c0fcc0a504c40fe820400de8400042a081c0050975025812d83f70807034625d03f5815209941fd80ae815b02b4204c26701c40ff01f8840b0227044c089411202230084010001f803e007a00ec0e50891081e10383e500000fa01c842a205430a8406540c0017102de07d40f901ea03ca06d40ec856609dc138c26c87ec,
0x10ff407280e201bd0358068c4b8081d10302050408880e101020143f4897703a625cc1c282e9094a23442f005df0bbc177408587ea01f003dc07b00f501e612644b901dd03b025bc1b8854d0aca03a807780f209200b7c17202e709220da40001fbb087a99fe3112b3712f004dc4bb04bb12b61fc013a880a0e7e113800081ac,
0x12a566550657000532ac21cc4bd092908181fa4110882103bc00280f281e0044e08981128224083c10682088000081c15cc0260048007a00d82a105440e42073c0e801d2000099fec4d152b2a5c54b0caa0caf12f210840f50051104c25904000045008808a02728415082c25943f400000a8615082698743119a07642b301df,
0x12a566550657000512f81f400fa81f203d407940ec81b5106020b4413882110362030000589a2a56001443a897b12c80114022041503b220683fe04da02de1fac09d016b02d0059c0b3016502c8058845f04c109ae1fa03f984d3101606d00ef87fa039407100d601a312ce207440c08141022202040280002625188944d589a,
0x106bc0cd024184d1097c0d300ae813509921fac495016b02cc214c2a407aa0a8a114009c813a02de05c40bd817c03180000fdd843d4cfea268003263e4c789bf1649ac915aa21965cbc39fa727ce7f9ca339866e38df71b8f1d9d5234a26142f286672f625f44b281b4038825e84b388110fd225ec2a180002625188944d589a,
0x1089c0004496093f1280250416e82cb056c1230241847606bc0d3019a04d1099212f80ad0144026215203d5054508a00000fdd843d4cfea26800326fc5926b2456a886596e38df71b8f1d9d5234a26142f2866260e25f800307a7013c01a4049808c04ea116421c8452089a113849f89401282000416e82b61258123023b02cb,
0x1086610c8000897f0a921eac3e589400a8a1140000289a5234a1794930ec61d90a1647661b7e13001680005800605100a703b3827c01260230139026d08b411a82298452089a11382a405490f541eac3e5854508a0000144d291a50bca4987630ec81d943b30dbf022112fe00183d3809e00d2024c046027508b210e4229044d,
0x1100020a0401082e100620c4402083400007eec21ea67f8c44a26ac4d263e10ea98f137e0cad5926b2456a8865913060cd025f0476026e0ad80001fbb087ab24432cb71c3b3a4c4542c0982000210cc227024d04ea260049f8450000099fd44d263c5234a17943329261d8c3b2142c898100161ee8126024b049209201230065,
0x105800bd400605cd01ca034c06008a1022c0c48083810606000bf815c00c6096a12b4257049f094011ec23d039803180e400be017b06fa05c40b78340027404e427804ec09d413ac27204e009c2136826104c110a615342a7056501e4124016f82e405ce12441b482f1093025e03d5054508a015083f9880d0ff820703ff0822,
0x103461fe0002840007e60fb840b0589042a081c10007e9001420501138226044a08901118042008000fc01f003b0394103c20707ca000025f04bc88530a8a11402a105430a881c840ea836903a607480001fbb087a99fe311289ab13454accaa09840866000412684390cbc01a44c0894113041fac4bf016a12fa0c8018c0304,
0x1556ca268a950873130c20a40f687e9084a25ec000040e00a600ec002858b0b0815f82bc85750ae415c011a89840a84150c0001fbb087a99fe311289ab13454ac4c288f511ce09d42270001125c052809b812c0fd604c409501290250049c09281240246224426204bb096c1fa04c187f40fe01fb8408080a100e00a00de81ac,
0x10fd807540e781b31018076040d81e410421fa44c30000556ca268a953b9713101f400c9818f02fc060c0b9813d0fd605ac0b3018c02f805ec0b8816f027404e426b84ec09d4139027004da09821fa026980002625188944d589a59a0b54964b2d56593cb378002acd3130e1fb00e981d5035206880d081a0102e20204028000,
0x1101a1fa44c309850a84214c2a6854e0aca03c824802df05c80b9c248836905e212604bc045000007eec21ea67f8c44a26ac4d098b12fe02b004d8069010e09d423204590872113422700004cfea26948d289850bca1994930221131413241a607f40906204016581bf00007eec21e88750cb2e7e1bee1d9d2a5aa4604c481d3,
0x106300c1016002f50018173406988a1029204581890107020c0c0017f02b8018c1fac25a84ad095c127c250047b08f424a80b58166073006301c8017c02f60df40b8816f068004e809c84d709e013b027504eb09c8138027084da098413043f404d30ff420644c408041006200840007fe0ff81fcc41a0831105c20a0411081c,
0x11044200841700003f7610f48791d8c3b2c7668ecc1d9c10ea19644c687eb02d605980c6017c02f605c40b7813a0272135c27504e009b413043f404d310041ff83fe07f30ff420b8411081c101a20643f48988130c15982b0898b10a60da40001fbb087a99fe311289a1318204049c87f409920d3024182cb125800044c50320,
0x12a4454b8ec990e221ce263c4a1094012822200445887810ea25442a381cc035c079c0db81db0ad0203040d8821000043d887210ee21e443c0ece087521d84389daa90e776ae54b44c705cd0018228408b0312020e041818002fe0570031825684ae093e128023d847a07200df41a004eb09c213082a6854e0aca1fcc40687fe,
0x12a5c764c8710991119a00002a101ca037a25ec2b3000010eaf055dab952b132023340000542039406f44bd85660fd8263840b07f81020133c3fa035e121c123024180e301a206cc40601d81036079041082c505b220283f804bc066811d848105cd0ba415342b282b000007eec21e9fb621c843b887910f03f70767043a8657,
0x121c6ed5ca968992128424fc4a009411118220443c89510a8e07300d701f303ce06dc0ed85680fd8264040b07f81020133c3fa035e121c123024180e401a41fa84c7880a0fe012f019a04761204153441681b31018076040d81e410420ac016282d90b9a17482b280003f7610f4fdb10e421dc43c88781fb83b3821d432b9522,
0x1000015080e5097b0acc1fb04c908160ff0133c1af048c01c4264416c836501d403bc07d049706ce06cc40601d81036079041081cf03aa20643fd04d30fd02634174898c05e212604bc02e705c80b7c24880f209200da40001fbb087a99fe31108753b26264c4a1087110fc21ac4398876110622240e601b70ad00000ece3b94,
0x1099e1fd03f807ee06bc243825e04b70918120c19a032901c6034423b07d20fd42408481854c0a9a06cc40601d81036079041082a3055e0b1016c05c80b9817442b280003f7610f4fdb10e421dc43c88781fb83b3821d432b95222a5c764487109950fd417382e485c50b8416fc2a68000b9a4439087710f221e0762c4ca07ca,
0x14cfe21d5d9b952b132e1f280000542039425ec2b307ec132420583fc04cf06bc1230071099505b00d9407500ef01f4125c1b381b31018076040d81e41042073c0ea88190ff4134c3f4098d05d22630178849812f00b9c17202df092203c8248036900007eec21ea67f8c4421d4ec88996131c1fb040b073c0ff020404050807,
0x121c843b887910f05136767043a9d9521d84388875bc152a5a266800602d0059c0000ecf1d8c3b2c7668ecc1d9c3b147648ec843a71332001839d087110fc21ac4398876110622243d505480a8e15a03f60997036620300ec081b03c82084000267f3b3821d4a91152e21c6ecdc4cc02250fc4103c0000542038825ec2b30000,
0x101b206cc40601d81036079041082c6000043d821ea67f3f6c439087710f221e0a26cfdc1d9c10ea195ca91152e3b2a43b1b7f899b115621e82d0007500ca001814b80ac050a026c0348276011e1194232045a08b210e4229845200022294446888212a21ea82a40547037e07cc0f381b703b615a0406081b104220b400010f6,
0x113180bc424c097805ce0b9016f849106d215382b280003f7610f533fc62210ea76544ce80061100222c43c05480f540000ece5ab61da43b187640eca1d98439c4ce07c8044e010801d802d005600a810a8979081e10381ff84000e4a1c903918722000015080de81b512f615983f6099a10201fd0487048301a61fa806e00db,
0x18c4421d44cf00061118220443c87ea13381d043a007b0034a201c3f704b70e740ca44a887aa0a90151c3e901f303ce15a048187ec1330265c40987f609960d5424480dd1336174c152854c0a9a0d941b3882d036620300ec081b03c820840e781d510321fe826987e8131a26644cb0993132803e824b80f201de03a824802e9,
0x112e0264840587f309840d0023d00c61028068840280003f7610f4ece08732a5c1964871899f09961fd81aa8813091226603cd07ea0ba0172c2e385c4001826744cc8996132607540e788190ff4134c3f4098d0a9a153816f82e405ce0bc424c02e9131812444ca00fa092e25e007900ef01d412401b4856500007eec21ea67f,
0x104000002c4d261d4c7a988ccb0000532b065586570cb032b8657c4d1857e12c82428484094912ca25842a187440e421510000263fb134987531ea61f4c4699f40028cae1970657065b195e13440150212894b046e0002c4d262b4cfa00146550cae197032c0cae89a112f215c82b300004cfe54b8a96152b195e26802b308bd,
0x10b1600b84d209a012ca258400007440e86150c2a107ca03da077c0e201ac034606f42b3092912e02038408881d105206800d081a2100a06a440400004cfe21cca97152c134a16104b209a21210268c4d08963129225944b085430e881c842a200004c7f626930ea63d4c3e988d315a67d000a32b865c09a4129408240ff020e,
0x1261e9bf131e82214c38ee5400289a80eea0d3019a0329099212f83c30146026604a02b280003f7610f487710f23b2c76688781d9c3b14b1c5648ad510cb2438898589a70eea0d3019a0329099212f83c30141025c048c2b280003f7610f487710f23b2c76688781d9c3b14b1c5648ad510cb2438898089a6129400a82c7858e,
0x10e7426a040881a5100a151c2b408ef0802000043986592a5a4c3d37e263d04420014767261c1354001400e80180084010001f803e007a00ec1f9040e000099fd31e8cba000626a402688af083c23ac0f3895000d410ec129002511de00b81fd84010ad006fc40705430a881c842b081b6027a13043f9880b000021cc32c952d,
0x1037e20380e608140a8e15a04d280003f7699fc87210ee21e443c0ece08732a5c875832c92fe26044c10983130826184388980130a21d8e4e5cfc09ac0fd422344ce094412841ce80db854712a215a000010f621c843b887910f03b38ecdc871152d50b643b07670ec81d943b307683b94135622d0030005c00b601682180244,
0x110e6196497f130226084c18984130c2a5a4c00985393973f2ee544d6890a046208c0026804c083e107847581e712a006d84d5802500ec01d003980720e8426a846e03fb04960918221027304e209bc137096c049c096c13a821611de00b80138402080200004d480011258150c2a10135029215843f5814b10a615342b28811,
0x1043e26bc45407ea135625104ce005e00b8016c02d00010f9c10b04a881b70e74151c2b4000021ec439087710f221e07671d9b90e22a5aa0e542d90ec77286dfe0c409ae008022b800c841107ec164411382081178009410703fb07f80fbc00009a90e861c882a18542027a04d40a4056109821fac3f9894d10160000989267f,
0x1101c073040a05470ad026940001fbb4cfe439087710f221e07670439952e43ac196497f130226084c18984130c21c44c0098510ec772826c444107ea135625104ce006500c8018c0310951036e1ce82a38568000043d887210ee21e443c0ece3b3721c454b542d90ec7728d4044d8006211e010c80005ab65072a16548c8ec6,
0x1260c4c2098610e226004c28876393913660018038006d00d810ec12908f50a901ea80005ab65072a16548c8ed2513299f07640eca04423b4076309b2135601d003980720884237012d8743049a10d80330242047a26c04b60001135e09104d7027304e209bc13702750ab823d439d08530a9a159440881a5100a06b840401bf,
0x10518002c13f826704c4098412f846208ae112822280a5012801fc03c89b205100a1404f045a08b215243d585420a86230839107400a8e000133fdab65076a0e542ca91950b6a0fd4238ed25133626933e26fd1d90a17811089b4135a26b042989a513620000fdda67f21c843b887910f03b3821cca9721d60cb24bf89811304,
0x10fd226784ca00ea0aca0ba44c600fa092e25e017382e4092203c8077849006d20000fdd843d4cff188952a89b604a410ec472806a13680002d5b283b5072a16548ca85b507ea11c7692899b13499f137ea67f0442a1784da8054084a001411c003a007000dc45e040c009a0130012801f041c10781fd83fc00001f2814b026b,
0x109c20df4250075a02901fa8264877406981d7c3ba8773066812f84d9813d0ac213043f587f3129a202c0db09b112a21dc4429854d079c05880b2016502cc059c0b404d7038c20440d28805035c20200df880e039820500f0881d03dc20a42a38568134a26984d3899f03aa205c3f404d30ff420603fa080f0fe020243f70806,
0x1120426cc2a6854e05be0bc424c03ce02c405900b2816602ce05a026b89a6134e267c0ea88170fd0134c3fd08180fe8203c3f808090fdc20183f4899e132803a82b282e9131803e824b897805ce0b9024880f201de12401b480b608dc0a9023789b600007eec21ea67f8c44acd487609b7136a079c0008820114a223444107fe,
0x11052207440c081710282044407880e1012202040308050fd226784ca02e9131803e81788497093025e017382e405be03c807780ea092212401b488530a9a15382b280003f7610f533fc622137200302e985d10ba015380005cd23b187658ecd1d983b387628ec910ed13701fa806900d109060b1800602af055c11d819a04be,
0x1010c26bc2258001136a04f4260856102901fcc3f5880b036c079c09c09b110401ff84a884e106fa1280180000c055e0ab823b04c906680d3025f09b7120426cc4dc02a4016c11bc23709b6134e26982a381ee03c207300df81ae034a07182b409a5133e05a00b3816602ca05900b104d70fd0134c1e707fa03aa1fd03f807ee,
0x121e443b88781d9c21c843b0ecd1d9621c426f4170800c05c426ec17182e0092426e806782c8090212082a6854e13280002e69043d556e43c887710f03b3843908761d9a3b2cacd04de07ea0b9417182e1854d0001734887910ee21e0439087610e23b1a26ec3f500ed01d803ac00010f621e443b887810e421d84389baf89ba,
0x1035206cc40601d81036079041080004cfe54b843a952c76aa2700000844b0872021803487bb10e221ac4398876110622242a381b70ad00000ece10e35136ee51dad3b432a5a26fc26e87e80ffa267c40f00003f7610f4ece10e38b8c54b843989be00180b9417182e205c20b8024909bb137415342a709940001734821eaab7,
0x1027404e43f4077f098407903fe01d80fe606cc410881c1036203440607e9137c214c1a0047a018c0000fdd843d4cfe7670871c6a38b8d173944d9310261c54a8a9709c210b20004005844b10c82188430085e10b8216c42d008612d221ac3d585490a8e0000ece10e33b1aa26ed5b09c1135200002a18542035825ec2b307ec,
0x13b3476584e287e9103a20300f101b90000aad552d152f13881d8c4e103fe0acc15842a0843c0ac6155c2a289c109420bf4082037109300bac1bb049d05ec03f01c504aa061604340001fbb087a99fcece10e33b1aa26c4e187f4102013100dd01450fd81fac0988130025e12ec3f8080a138026fc415880102e205bc27384d9,
0x1074e1fc040509c003c2207c3fe84dd0fd013083f9880d0fd226f84e204550866000442c824600162190431086010bc217042d885a012825a443587ab0a9215141b3045013860dd824e82f600180b9417182e205c20b801a0049208f403f007480c6137a15381b409b9132815940001fbb087a99fc87910ee21e0767087210ec,
0x109841fcc406834008f60aec0001fbb087a99fc87910ee21e0767087210ec3b2e54b843a90e9138e07244cc081610261fe03fb04cf09960d781aa848c091203883cd07ea0a9a159416882da0fd013083f9880d068011ec15d80fe01fe0000fdd843d4cfe43c887710f03b3843908761d972a5c21d5b8110e8138c04dc42c04bb,
0x108f60aec07e09c6138e0000fdd843d4cfe43c887710f03b3843908761d972a5c21d487509c8000c1ce83a087400e7e2230440887912a21ea82a40547034a07cc0f381db0ad02700409880a100e1fd83f807ee099612f025b835506680ca424484760fa402c806e00bf016a15302a68565054c0ac8168880c1036208441687e8,
0x110141fe03f804cf09780d7819a048c08ec039406009c801f827184e387e809841fcc416882110362034406054d0aca0ac816d034008f60aec0001fbb087a99fc87910ee21e0767087210ec3b2e54b843a89c9131c270040b080a0ff01fc026784bc06bc0cd0246047601c624083f5054d0aca0ac816d07e809841fcc4068340,
0x1039820500df880e0a8e15a04d287e913920000fdd843d4cfe43c887710f03b3843908761d972a5c43884e580c0120611d83e90334065212f025b854c0a9a159415302b20fdc20183f8080900007eec21e90f23b2e21cc871065713941e9c43d8942127e25004a0888d110425442a381f303ce076c0db81cc035c15a04e00816,
0x121dc43c0ece10e421d8765ca9709cc00e426ac22108dc04b61d0c12680ae0144094c122023d04e609c4137826e086c22a4233045c087426b813a855c000223d4219006603ec07a439d09b0036e20bc411880b10061ffc3f984ed09c413083f409ca0a9a15941a0047b05760dfc2518305072c12c818c8811034a20140d70808,
0x10fbc15082a1854c0a9a15602ab855e036020200e0880e039c2050000043d21c443c887710f021c843b0ecda67f3f7621cca9790e80cb227383f409ca0fbc03f03f4849d101827100dc89cc08f60be015d80003f7610f533f90f221dc43c0ece10e421d8765c4e68376093a26f807e09cb0fd2272417c00003f7610f533f90f2,
0x10e440002c4d26fd4cfe99f131e89d10fd4034c068800021c443c887710f021c843b087b10e86fba274002008ae08220fd82c88227041022f01f787220e8608381fe002507f600004d485430a840002c4d267f4cf898f465726fd139e000048289a905b80b2415a048c090611d807280d301801fa818102be11a6128023d8897,
0x11018151c2a407aa0000ecd6d5b152d50b20884002887513aa002c120824d0498092c1248248048e091821604330a921eac0005ab64c78a16541c821f13a81d241ee81e8104420843f489d20001734952a2a7b3f74274c3a483a1034e20184028000b9a4a950fdd087313a422f0104020e07ec0ff000c8000139e26a42a10543,
0x104c609102310457089411143e700aa0130021403f00600a86151039085470aae0002c4d263d5072088541da85b507ea11cdbfa67d000a32b8cab195c1daa275812987c4051822ac2d0007500ca001814b8285013c09d8049806908ca24fc22d04591280114c229043a087207cc0f581e70f60076c0db87bf105a209c410881b,
0x1556e27683a483ce03aa205c40c0000b9a421ccfdd2ab613b200d4002840c0b0a08782a18020004200880118024004c0002c4d0005664a98fccab89d812ea25904a4896512c2150c2a20721004000840110023004800983a20000b134001533eb3254c4698f531fa61d4c3e275c00505900b1c162c4d2074412c20a58141026b,
0x102d205a00b3816602ca05900b104da0982135c3f404d306d0214c0002ab6513499f96682d5259a67eec4ef098803a2000155b289a4cfcee5c4ee800c05780ae80001d9e3b147630ec71d903b247670ecb1d9a880a27700030089011015203d50000b56c3b187640ed21da03b50767354313b600082468492000010fa203375e,
0x110181fa440b89dd0a98153407500ef0001734933f2ab66ebca2684f087ed06d40df826d84e20000b54966b1fba3f547eb8fd81fb43f6c7ee032c89e00fd605bc09d016b02d205b00b4016702cc05940b2016209b4130426b87e809a61fcc40687fc10381fe840c87e9102e2774000267e556ca26a31109df0fd605bc09d016b,
0x1065c0c902a5080c1036000021f1fba10ea195c97f130226084c18984130c26244c38a9793103f66278839e87ea10261bac37006d60da61b4037a07f60fd6132c41f03510fda1cd80b5816c02d0059c0b3016502c8058826907e813c01e081b3036406c60d881b0836013be1d244ef03ce0ff41ffc3fe07f31032209440e080d,
0x1096c1b9437006d60da61b4037a0177025c048c451016c09a406e43a483ce0ff620303f489d90a94124c0002ab63f74195d669930113c8124000100ea0ea21f982a6854a0926000155b2b36556843c887310e821d443b08772a5554ea43884f187e40e7a06c00d388131014201c37a07f60fe01fb83f584cb097812dc41f0351,
0x1556c43888792a7554aadd78ec51d903b24439887610ee21e010f6243448a88090f2a1e94412890b0f1d33f09e60fd40458083810601f403bc07504ad093e125c248000208d6240c2a6854a0926000155b2b3621c443c953d2a8254aa43a84f28002093411e807e00c613c607880d801a7103e202840387fd0fe01fb826e04bb,
0x1092606c40d404a603d8209c25a81fa106612800f40821095c07d041684b203ee20c024882bb08f606e44060000556c21d487110f22a5ea9d552ab7dc6e3cdd78ec51d903b24439887610ee21e010f624343c50cae4c2c4f38000119a1f4016e02c906340c5818102be06100bcc3af02e90a822784209054a0926124415d8000,
0x113d21e2c17482e706cc05a43c10000b9a47ee9dad3b6221c443c8a97bb55766a762887744063b2d188dcbd930f13d0001803b007f00d0019c032843d088c10c8000893f128026284a087aa0a90151c18c030406400bd416e82cb05800ad817485600f160b9c4f3048c090607380e0881610201fe03fa04ce0988056c0a3054a,
0x1262227a8488084f109c21303f589e813ce05a00b3816609a41cd83fd081903aa06c40d400d301ca03b42e485cc0b9a1b6036a86d7016802dc05c00b9016c12602488476057611ec0010471018027940fa082d03d0208445101b910181fa44ec854a09260d801b103630000aad8fdd130026244388879152f54eaa9563118657,
0x150bca46944c28661da43b4076a26fc523227b03af06d90dba1fac4f007820b9217302e686d80daa1b5c05a00b7017002e405b017109b427a81bf04e20e6c0002e691fba5aa4b358980131221c443c953aaa5521d610f61e51d963f547eb8fd81fb40cb24c289841fb813d61fb4427884e00007ee8fd41faa3f5c7ec0fda1fb2,
0x1093012980f60827094012b825901f71060124423b02bb08f6000823880c013ca07d041681e8104222880dc880c0fd227642a504930000aad8fdd130026244388879152f54eaa95631189ed11b800181288069052e02b01440285013609f013b008f087410e4232846408b411642298452000222942a385480f540002d5b289b,
0x100001f40390054205680c6818b0302057c0c20179855e111a22084a8875e05d20e3819f036f06f60d982b209eb13d405f00b8813a06fc13ac27004da0984130426d84e209c21fa04f4836306c40d841b0054d0fe620343fe081c0ffc20883ff8825100420b839b00d30b9217302e686d80daa1b5c05980b4016e02e005c80b6,
0x113100794427885206ce20843f9880d0ffc208800046223f724c0098212fe2604aad843aa64313de1d241ee890b09400c00163000c05ce0b9017884910930153806985c90b94172c2e605cd104422883f489d9000173488759d9c3f74aad933f843d13dc1fac0a4014409920d284f607f41020070424182c91178081c10103f3,
0x10930000823f01c110201fd0262834a0a9815382ac0564037220300f4082103d8209c0fa082d03ee20c00001fb90cae21d4a97ab366fb899fd48c09f103821d2440803ce0fe81fec26484d5029005a83f489d90001734a35026fc3f74aad933fab340cb24c3c4f807eb02fc04e80b4016702cc138026084d70fd0134c3fd0819,
0x1092e000823f08d70a9815342a700cf01ac0360000289ab9a4aadd59b2ab454f4ace95412ac26fb899fd37eab3513e41f200168215044e010801f803e007a00ec1ff8400081e103800007d00e4a1c90391854206340c58184030205e60b2415f055e00180b2c162831206000bf815d82b805e20bac24184b2095c1298250047b,
0x101e8120823d849f08f4125c0005cd2556eacd955a2a7a21e0a46537e90f2566810f44f987c8005a08541138042007e00f801e803b07fe1000207840e00001f4039287240e46150818d031606100c0817982be0abc003017409da13740b14189030005fc0aec15c02f1127c033007a0483096412b825304a008f61260256847a,
0x102de04e809c84d709d813a827204e009b413043f404d306cc213c42907f3101a1ff040e07fe104420004140802105c200c41880003f7221d537eaab659a6a2684fa89bb0baa170400600ee05c60b8817082e0091a12382a700cf01ac0b041640000b9a4df70879043b3b387668ecb4484556e27d04de02cc05940aec08380cc,
0x1091c0002e6937dc21e410ecece1d9a556e76584fc000008000ff010a820e00009bf4003267c32be27dc3e4002d042a089c021003f007c00f401d83ff0800103c20700000fa01c9439207230326063c0c18173027a150421000004cfe9bf5cbc39fa73fce519cc32642261e27d84950420029227bc3f58166031805f00bd8171,
0x1039806dc3f601ba102c20403fc07f409a213241af07d3121e27800d9880c03b0206c0f2082106f00de427087fe10440df827107ff104a0e04272880010500da826d87fc103805100ad0837000021d432c93075668a9dad5b0ed41d983b487670ed01d9454a8fdb0ec83f7027e400602c213e8153816f02e005c20b8817182e5,
0x1102c1fe0268835c12840cf84fc81b31018076040d81e4104213083f9880d02b4000043a8659260f6ad8a952b343f6c3b4876a0ed01d903b287660ece54ec27ec3f804be10140cc00d807200e9222f01a609f70e4415081a4836d0678158826d87fc103813083f9880d00009bf443a86597271734959a2a7443ac7edc4fd0942,
0x11da03b207650ecc1d9c54b84ff89d00e900b6816c80e701c40b3016502c10916122824000020902035406a00d201a015302a68000b9a4acd153ba9194dfadf744ff094206b80cf80004620b56c3b4876a0ed01d903b287660ece8bc67ee44fe83c90ff01d24268835f00001965c9d5cd254ee54ba2f109fc0fd807300e701c9,
0x10896000421c8942037e06dc3f601ba10201fd0264837d06800dc448789e013fa27f00d9880c03b0206c0f2082109841fcc406837806f213843ff082206fc13883ff882507021394400082806d4136c3fe081c028805680b308370a8e15302a6855800d2021800307aa0a9027ec00008750cb24c1ed5b152a56687ed87690ed4,
0x110ea1965c9c5ab61da43b407640eca1d983b3953b952f3f7243b887610f021e4a16810fc1e884d2aaddbee043b140022f011509f70e441058000025305e61f284920542092c0b70173055e01e827e03f500ee05ba0b6807300e501c8038c246848e0916122800109f301b0035806789fe06d0135c3fd081903a624e421f0438,
0x1b56c54a959a1fb61da43b507680ec81d943b307670a02125824f420202cc13e612080005cd25668aad159b2a7a5504a46487810f2043eaadc21e8a0113a20934129800b049810cc19904be0fe0202848d81b005b80b982af047113f0240816e82da01ca1238245848a0a921eac2a6855804a2095012a825604ae09600678000,
0x109ae0d9821f04380896000421c8942067c1bdc37706e30dd00d28487834c09921fd040801c103e807a00ee81b913fe05844fd808600d20018406081b104220b426107f3101a0de01bc84e10ffc20881bf04e20ffe20941c084e5100020a01b504db0ff82070098814402b405982a385480f5415302a68558000021d432c9307,
0x1260e54a959a1fba08771a8544d291921e443c155b8a04069027e8501094106640dbc25f04db0fd013103f808580fe820280e008100360070442b88560a8e1560098814b02881ff040e0000b56c4c1ca952b348d42a464ece0ed41d983b487670ed01d94a9d043a952f140603404dd00e21400123424500021402262040c87fa,
0x109a41fe8401880210001ffc3ff07fc0fe62064418882e10502094411081c101a1fa44c3098802cc20d841b834500004c1ca951fba8d42a26955b0a050fd0134825c87fa0fde0f3c1d0874914061fa44e9046b08e221c843f8877110821d04450903120426e807680e905d01b8c374048d091c05b42a68558024c05980005ab6,
0x106980002d5b13072a54acd021dc6a15134281c4fd034807421fb43f78381097213940930131106a20d841b8345068c200041407e913a40d300005cd2260eacd23509fb854e8a95032c8a06081e089c00008bc0fa027dc391054206c80d201c6836d07040de819e03930ac427801b3038109ae13b427584c209b6139427087e8,
0x106980002e6913072a54acd021dc6a1523028243f601bf0382073c0f201d80366204040c8821103620303f488180fe81fe826204d20288059800013072a54acd148c0657141007043a48810079e1fd03fd04c409a41fa050307e913a411ac238834a1206240850200ed01d21bdc37706e30dd012340b68a050a9a15600a20166,
0x13f70282840b01ce0ff0122826880e206b6240806008cd08e200004fd07d00a840d201c6836d07040de819e03930ac41fb41b584ed09d6139427084db0984200c40108000ffc1ff03f98831105c20a0411081c101a1fa440701c10e920ef03fa84c80fd0282037706e30dd0224844e034a0a9a04c40ad0835106c20dc1a28346,
0x109841fcc40680007274acd148c865910ea54bed5b043b3f72438c5058902019e11c424009fa05981b741a406ee0dc61ba042c07ed112422700988835106c20dc2a6854a0908052c19c84c20fe620341b584db0ff820701bc84e10ffc208842b085703800d3026487f4102007040a20000260eacd148c865910ea54bed5b043b,
0x1141e06f850189ec110021e044581c100004c1d59a291910ea54be350dab650bca46944c286654e83b287661d9c1da4a26c8738a0e13a00348068000021ec438887710ec21e043c9bee8a0d1204030000010f621dc43b087810f221c4dc7450604d10ff027f440b087110fc21ac4398876110622240e702cc0914120007100cf,
0x111181fa8507036609ae1fe840c81d5091a25444dd016606de136c3fe081c067c13083f9880d12800dec27087fe104424fc19904be0fe020280d804711418282c0ad06f70ddc1b8c3740852069813243fa0810038205102a6854a090804c41c70a0a09d62008417054700004c1d59a29190cb221d4a97dab6087643a8ece10e4,
0x11108222850785480f540cf826107f3101a25041b784db0ff820704a0037b09c21ff8411093f066412f83f8080a036011c45060131071c13ac401082e0a8e283437b86ee0dc61ba0429034c09921fd040801c10288282c505015a0a9a15282420000260eacd148c865910ea54bed5b043b21d4767050801be140627b04408879,
0x13b3a3b4876a39391426000422c843d013c01d800029190444a1787688a12039c205824587f805ba13444a109fd067c13083f9880d0000e4e832c88752a5f6ad821d9fb91d903b287661d9d1da43b507680ece142228000e709df087c10e040b0366125800043fc09ec0a8410e426881be0acc01a44a109fd1406001843f8877,
0x1142812384ef82e806cc27b045e020704040fcc4d480000e401f402a18542026a064c0c7818302fc05cc09e8561126404c42720800105013b04018831027413040b784da02f605f0270018c09d4213c429036f09b61ff040e033e09841fcc406838e09d620084170a1206f613843ff08220a8e000148c865910eb6ad821d9fb9,
0x10ffc20880c604ea100420b82a385490f56213c429036f09b61ff040e00005232196443a952fb56c10ecfdc9d9d1daa285840501b00fe011c825f02b60664000032c88752a5e10ecfdc9d9d7270a16050a8001131424b04ef848e05d00d984f60a120a8e000148cdab608767ee542f291a524ca2614331d9d1da43b5000326fc,
0x10ffc20882a3800052336ad821d9fb93b3a3b4876a065910ea087c50c0001087a10e403b806f0000a46411128981da6285c4fb093213de277c098848e04b628541740366087c10c82258001001611482da85b40b6616c82d885b00b5e024c046806809c8200041404ec100620c409c813a09821fcc406816f09b405ec0be04e0,
0x10cb221d450c881613201fe00df04d11310056840c87eb0ff427d84fa8a14084027bc4ef848e13fa0ba01b3007500e801cc03908a5087a213c429012d0264284c2720800105013b04018831067c130809d04c10fe620341b784db02de05c426d07fc103805ec270038e09d606302750802105c0e5c2780804106828481bd84e1,
0x1117800004fb87220f88150814602530ab8002c46e05a0011400181288069052e02b01440285013609f013b008f087410e4232846408b41164229845200022860509038e07060dec1b7833e09d6139427084db0984200840007fe0ff81fcc41708281044207040685470a9015243d507ab0000a466d5b043b3f7276747690ed4,
0x101d603c005c055d0fd01bf03f586f40df0213c37b06f70df21bcc37d06f5120611ac4e900e901da123450d8367143415342ac056410a4000021d9fb93b3a21ccfdd152e143827641b40000b9a421ce311aab6143626944ef81d5091c074c1740366102e000021d9fb93b3a21cd44d0a1a091c277c17403660fb609d02078227,
0x1039007040d80a1c0e4215102a185420174157445d0903017002cc23589d20a9a202040708111028207441480e901d603b007680ee01e0123450d8367143415602b2000008767ee4ece88733f7428741d804780fe60afc26081b7027a26b44e881360292031047d847107860ea01de0749134a20244078812117402cc07600ee,
0x101741574089010301d003840620903094e126824508fb090a11c423581f003c407380e401c10360069c000043b21ececd5daabc15766eed5dd9dbb4321c443a933f952f143c00444d203f10b200800005020d041808241fe89d712ca2584000074413522744089010301d0038406204a70934122847d848508e207c00f101ce,
0x111f6121423f033407140dd8194835e06aa0d30199838906ea0ca01ae8354069606b80f701e1034a07300e301bf134a28782a685580ac82014404080e1022205040e8829000010ecfdc887321c443a887610f03f7699fc50f801113480fc42c8020000140834106020907fa275c4b2896100001d1039085440a8615083e889d1,
0x1772e28840d289700650069c194846b120603c40e88a1f143a03c007700ed01d2123450d83670344286840b88050a9a15602b2000008767ee4ece8873144000444d203f10b200800005020d041808241fe89d712ca25843a200000e4215102a1854213a21f4405d055d0188044808180e801c2283406a8471094e1268235848a,
0x103f80fb800001a3036a25ec40607f3101a1ff040e0802105c15103908541109e21480000875000cecd4fdcc5e02a56289000509f70e4a1c9039187220e4c151039085410000001933e19604dfa288c48100c201dc03c000010f621e443a8871375f6e3a28883f601d1039e06cc40601d810360790410800010ea99f8a97152c,
0x105fc0c0025001e810420c4825701f4105a0002e6908754c7aa169d9a952f54ee10f48721d8c3b30a9d0513000c05b20b5815402aa054e0a9815282a305440a84245846c0000767941c261c54aaa9dc21d8a25126404d4098818c02de04e825f04ea09b413043f404bc02f805ec3f80798101406b01f9820512e808040ff81fd,
0x11062201041a0852114415602ab854108240ccc1938367000099f843a95223f727eea2f028385136b34d31e930f1450283023b06fb056c15344290000b9a47ee4fdd2858261e10f487810e221d8a9d48771d9d144e0b74006048c0b9a039444f00c5056a11d023a854e018c11e80830107093e045825682b8057611ec0dc880c,
0x1040e081410202030404007800e801b0034006400c035c07e60fc845d800000021f4039008a4072e064c0c7818302fc0dec0b9836f027a0cf827804ec09d4139027004e109b4136c26084c20fd013480b181690a86151039085470a98153841681b310181fcc40681d810361ff040e01e410421ff84110800105020084170803,
0x1145416080050005040400601f983f20a8615103908000b134000ccab195832b46578cb00caa195c32c06590cb6197098f451489ed127a1f9c51380cc144c0bc41758107018c03e807a0498093e11e824b8002144a07d00f401b9039c069c40b07ec0ff0069451204d1100e05743f704090f0c00d4095000507dc16080ff800a,
0x1261c4c2851604c9069405104f607eb071c05f01bd817106de0cf827584e009c2136826d84c2109e21480002cd05aa4b25964f5ab61da43b4076a26fc5136b544fdc930026084bf8981130e2614196451587eb026a04c40b8813a097c136826087e802f812f03cc000059a0b54931e3b5459224c40989130026084bf898145e0,
0x109a405200b48a2c0dae1b5436c06d606d00d9c4290000b9a4b3416a92c96593c43aed5b0ed21da03b5133f26fc556ca26d669ad5126147ee451707e8098212ec09d01330000b341648930b145a1fac0b4016702cc13483f40a2b109e21480002cd05aa4b25964f5ab61da43b4076a26fc5136b34d6a89fb926004c1097f1302,
0x1022c0c0017f0107020c03e807a02bb0570033006304b2095c12b425304a0093e126024b847b08f407dc40101f403d81ff80f407fc03ba1fcc0dc8830105c20b441388221042207040d880d101821582a6854e0fce15a8000152f54aa10f4ece2a773b18766043a8a2f13d80d281c7037b06de0cf826484eb09c2136c26107e8,
0x1121e27a8427084d1098212c4250849109021605170a2d0fe020280d80476056828a43fa08100ff4070440c81d4090627840ea803a007200e001b8036006a08881108220043e0878164893d0812102846687ca0000223444109510fa0155c2a1031a062c0c2018102be05e60b702af000c0918173407289ba0fcc28305068312,
0x10cb24c48fd58a3200001058207822a044e288c1b6833c00011882351267f4dfa0018fdb8a31139c26f415d80cc0e7a03e807a047b08f406e049e88d611ae125c3ef0896112e1f802a607e70ad420440e0880e03aa205c000152f087a767043986593f7628c04f6014a032005d409f817f099213a826d04c10f301fa019a090e,
0x10690135c2648167028a1fd040787fa103015082b1000010e6196631046a23f6e4c2451a83641462135c1a4016609921fac51987f4101e1fe840c084e0a84158800008732614196631046a225fc4c00986130e26247edc9811304261028d03f581440284000098512fe26004c30987131226084c2098839f91466224c4248000,
0x1000021ccfdc06593f647ea0fda1fba3f6c4c0c51c0a3106c80d2026b84c902c828cc51a0a36146a150819e084e0ac41fd040787fa10300000439930a0cb3188235112fe26004c3098713123f6e28dc3a1834806600c9826484be0f0c050c09801250fdc20183f808090fe8203c2b1000010e61964fdba67c260a28d85188364,
0x1880843888772b36147627681730a220180103c23b000005681058390022a044e15302a685420abc0002e69043d21e4a9d555b90e23b369bf8cb08a3a146604942648786109620e81a283230fdc20183fa080f000021cc985065925fc4c00986130e26247ec451c87ed065a0c8c25f0786025e04903f708060fe020245190892,
0x10fce0002e692a55087a7670ec62a75566a43888771d8a3b2c766851e894200ec01d403a00730884096c47a809300d2114821c8001125c285c4a0854700016ad942da91950b2a0e544c291a4df828f050680d409060b245118a3a0a840af8179855e0eea03e824c04970a9a1f9c15c02bb0001734952a843d3b38a9d559aaab7,
0x14cfa088452087ea0196032806480c8018e000087b10f221c443c0877375d148002cc45d00ee01d803ac3e9049205500b983a189d10a9815342af0000b9a4a95421eaab74dfa43888771d9b4cf843c131e8a3f0e860ad015404760fa4030c05c855e000010f952a843d54ea9bf4ecda67c21e228f846885e00bbe17782ee8775,
0x100017348ece1d8c3b307658ecd10ef148a290c15e847c148015343f38000b9a4a95421e9d9c54eaacd533e2ab521c4765887810ee148826502e0077500007670ecb043db9a4a95487910f021c4a9d559a90ee3b34290c04309af08960002d5b289b5232a16541c821f148423d41298069087410e40005ab65232a16541ca898,
0x1000229080b584d20ff420602a3812c096c1fb8403013709761fc0404814a09881fd040785630001734952a843d3b387630ecc087354eaacd555b86573f764c4544c291a148e176c5218a3d148a28e84e507e70001734952a843d3b387630ecc087354eaacd555b86573f76658537f10e2148c00302ec85d80bae17582ea054e,
0x10cae7eec988a8981496290c52287e70001734952a843d3b387630ecc2a75566a43c08711d963b3429283a1825b049a091022104360f9c01c8031005a0a820ff8000291950b2a0e411102214cf86dfc7648a4910d625a40005ab63b383b188718a4812d2291813f0a2308a628f04a0815f099c1fe040a83fe148223d40348439,
0x1b56ca46542ca8390442a264871267c3b363b221350ec614980b242418a2301aa28e851d82f3057a29284e50a4801f4126024b837109b205d452383fe00d2290421c87e70002290809604b60fdc201809b84bb0fe020240a504c40fe8203c0b584d20ff420602a385630001734952a843d3b387630ecc087354eaacd555bad52,
0x1025804dc0a5015f02d6158c2a6054d0fce15a840881b01010070440701d5102e13483fd081809881fd040784bb0fe0202425b07ee100c13283fb0812099c1fe040a80002a5ea95421e9d9c3b187660439acd05aa4195cfdd9311149a110803b825b1364288c037006b147410ec13f025211ea0ff80005cd2087a43c953aaab7,
0x110082000419082603f40e600f60385056812d025284760242042c0618a0d090603e0164849914460bc851d027404fc002c133826104c0097c12f044f0894111404c808600fe01e4526027c04ec114c4a0817509b215781ff0371147a1dd851d82bb0570033039e847b08f406e01a0077f027e292c0008a420f5615242a38156,
0x1102a1fe840c07fd103c200441500003f7421cc32b8a4f002226901f8859004000028106820c04120ff44eb896512c200003a209d113521c842a205430a8405740c50179025405540a4013502d21584000397b73f2e4e5c8cb91b7276e47dc93930f149c1ff841004df03d00df42500302051605fc22d89530336061027704e3,
0x108f41cf40dc880b0fe6130409e854c0fce15a840881b01010070440700002a5e767021e887354aa1964987a67d14a22248429085000007ee89898a50112421485198a4e13d40cbc0a30141068c0d141a20342068205a00b3816502c4139826e04ce099412d825e04bb0988131426907ee100c1fc040487f4101e1fd840907f8,
0x1097c04d44e8854c0a9a1f9c2b508110fdc20180d808080fe020240e0880e0a86151c2ab8201044e08a82c88a2314a215082b080002a5e767021e887354aa19649879fb94dfa99fc52982bb149411ec39e81b90a9815a8000152f3b3810f5d9baa5554eaacd48781d8c3b307669dca0a520bb8290c51e82be05760ae0066047b,
0x16e3a295406007a5016611d83e902b2054c15302a68000b9a443c821eaa5554ea4388ecb8a5401801e9423b07d205640a985250a4800d210e419f04c20fe6202c529000113a80bcc17882eb01f403d01938498092e1e180ee812a10340fc43fe001009b400140b9803f007c00f400e0025003e105820883f407f60000199040f,
0x1556ea95d53ba67e3b18438c52c07d2055002e03a18a44056828f852b02b308ec295452a054c0fce0002e691d9c087aa95553aab35b1349bf533e1d8c556a438852b85db147a29285228a540fce0002e691d9c087aa95553aab353b184388ecc1d9a14ac291006180c214a81f9c0005cd23b3810f552aaa75566a99f155a90e2,
0x13f7421cdcfc930f14b413683fe0173103428e80ee8a3d14760ae0066047b08f4295c52a0a580fce15a80d80808038220380e40811039c20505118a510a841584000152f3b3810f4439aab754aa1964987a6fd4cfc763052c800c05cc0b6416902d105a00b3c16709da091812242df80e901c403642a6054e00017348ece043d,
0x1089e167c2ce808a0f9623c847a08f611ca23dc12d025304a201a4220843a087229042a487ab00016ad933ea83950b2a26d44c022114b61d7816782ca05760a9015009c10bb817542e785c305fa0b3416102b9054229641b304d702d2294c2ab81480f0415843f389d913a415a80d808080ff420603f40a4f000054bcece043d,
0x1000054bcece043d3f7421ccfd9130d21c4297445a005a011a02280448088010c10ac225800114b622741b30332064e1fb419e04c20fe6202c0dc847b057c1cd85190a50107e2100421078602521fb840304be02681fc040484d702d01fa052787fa1030151c2ab855e000054bc21e9fba10e67ec89869d9b4cfa2970138800b,
0x1108020fc0cc018102e2057009a01290a98153839b09d90ad41fb840307f01012072040881ce10281fe040a81e2103a28c852807e8149e0000a979d9c087a7ee84399fb2261a297806a848314760b2415e8a2314b828e82a102f30abc29583f389d913a415a80d808080382203817582f10930077440d07fc09b405c43f40a4f,
0x106600114022023b045408a03f68415085410584fe800010e221f8435887310ec220c44487ca0aae150817d02dc05a60c78179855e098400303f982d905a20b40405849d0918122452c073d0b7e03f007100d914ba0c7018302f105d612d4253049803f407b00ee8832104c206840208000ff813bc27204da09a212f83c30842,
0x11d9c3b307640ed01d944c38fd8130026104c10fdb130214c4288c1a4033c0001188000346a132c07edc5308a33028a050c0a0800026244bf8988130a26184c39cfc8a6010161cf43f987ea09821b4837506e40dbe1b5436786ca027215302a6856a14a020443f40a4f000054bc8791fba10e64bfc52f84a012000c084b10326,
0x114c828e04fe832509a21e180ac012414c41cd83f708060fe020243fc081506720d142648a6014a01fd040787e8149e0000fdd087325fc4c409854620b56c4c3076a0ed21d9c3b307640ed01d944c38980130826087ed853184d113fa056847e87eb1464294019c80003f74b245649865925fc4c409854620b56c4c3076a0ed2,
0x11da83b487670ecc1d903b407653541261c4c0053307ed13fa0c94268878602b2049439b07ee100c1fe040a8a3214a01fa0527833906880d140001fba10e71882d5b0ed41da43b387660ec81da03b2a3509fb6260a29940ee849810340bcc3fe036c09b628dc000152f087a4c48439865925fc766c985462026184c389801fb7,
0x1000054bc21e9fba10e64bf89881d9b261518809860ed41da43b387660ec81da03b28002b54169cc4c385338001114a10e41b3034a067c1fb419284d70f0c059c0938a6314ca299039b07ee100c1fe840c0a320672151c2ab855e06880d142648a6014a01fd040787e8149e0000a97843d3f7421cc97f13103b364c2a310130c,
0x10b7e03f007100d90a9815384ec89d20fe020243fa080f039020440e7081403c420743f40a4f14be1f9c2b500002a5e767021e9fba10e64c408718a680002115421c8374067c23f8530822a082c0bcc24c01dd10341ff026f04da02ee05bc53303450992298039b07f4101e1ff440f0a3214a01fa052783390a84151c2ab855e,
0x10f54285c2a385570ac20cf80002c930cb318809879fb94df8a4647640eca1d983b3876a0ed014d2000421f034a08722318264833e14a629683c10a67012801a4000087110fc21ac439887611062224524054714bc1f282ab854206720b702af04c2145a296000607f305ec0b6416902d105a00b3c167080b093a1230244873d,
0x1087c0d98225808606a6110c000843900d201e40030a170a8e0cf83d505480aae15843c100003f741966310130f1d903b287660ece1da83b4148ca6fc14d6248017182dc05b60b6816c02d601ca1238245848a000424f42a60000b9a499f931f2ab7566caad15412a773b3829a821f0001118c10e40ae806909a200184fe8548,
0x111ae1e5424484920904000816a02e805982850535073d0390204c3fb04cd039c07d00f401b902aa28840e6040510322058451082d1042206c406002f00001fe83f480050802135c40a86610cbc19a833a866f0cc6199847389df02d21fe012d891b125829a42a105430a9815342ac094208a2023822c009908c602ac23400af,
0x12a5e29c03f48a2014320002d5b0ed23f723b5032ca9193b3a10ec53789f509aa1fa40b509d913c227683c1054c0ab0155c2b080003f741964987a89a4dfb1019baf0a6e103a1fa40f108a2093a125c07e80f400007eeae6943aa2a5e10f48728a6d1388127423d0101019800021d5152f087a43bc53608ba01be03c046b08d3,
0x11144127424b80fd01e826e8538874914e01bec0010a6f01d203c00770a6e05f60b501740a500f0415302a685580aae15840001fba0cb24c3c76a29191da4a26941d283e4dfa767453907e9102420341e183b1091211e806f80cc00010e9821ea1d721de29c453609ba14da153407700f001d20000fdd5cd28754dd7c21e90f2,
0x10cb24c3d44d283a4dfa767021e8a75127a277c4fb017e09d813a827204e009b4130440183e7100420003ff07fc07621fcc4510831105c20a0411081c101a1fa453987490ab0155c2b083660f040000fdd0659261ea26941d26fd3b3810f4a970a7412e007180d108be102220140000659261ea0e8a97087314e620783f483d9,
0x10ffc1ff03f981b9114420c4417082d1050208840e080d101815082ac05570ac20d983c100003f741964987c5e251349bf4ece152f10ea29d849e89df13ec05f827604ea09c8138026d04c1100620080fa08000ffc1ff03f981b9114420c4417082d1050208840e080d10181fa452d0a740ab0155c2b083660f0405240001fba,
0x10aae15840001fba0cb318809878ec81d943b307670ed41da0a46453c0a2201da03a4238848d0360276440407e914ec15343f385580aae15840001fba0cb24c3e2f1289a4dfa767021d952f14ee20583fc01ce09a229a80ae88cd0000277c3e089f613ee063c0c1817e02e604f427604ea09c8138026d04c1100620080fa0800,
0x1262419649879fb91d903b2876621d710ea087d37e8a79079e1fe84ef84d713ec24a80bf04ec09d4139027004da0982200c40108000ffc1ff03f98831105c20a0411081c101a1fa4539874914ee000853a8a72029229ac1b304550886112c00084390128021803c8069000c27f450b8a500a840cf83c105470a901ea82a60558,
0x100de01a42a407aa00016ad87640eca1d983b3876a0ed06a8029ec3f601bf037a06e840807f4099205200d9880c03b0206c0f2082100001964987a9188d4054b843aa6fc14f40f3c3fd09df09ae0d980b4892b13ec05242a1056109821fcc40684da0ff820702720800105013a8401082e09d8200c418817e09c01ff84110000,
0x13f723b207650ecc1d9c3b50768291810e63b4853f8a7d0e9229403c105580aae15840001fba0cb24c3c7640eca1d98a46010f952e14fc25c00df81a2117c203840287e914f8000032c930f3f723b207650ecc5230087c989152e43ae29f453c8a7a069400009890659261e7ee47640eca1d98a46010f952e43ae21d453e0006,
0x11d943b307670ed41da0a4604398a8013ae0fec1fa03ef003e005c007817902aa001426f04cd0cc2197833506750cde198c333000006e80d4c12e08cd08aa110c21f815d012801e403884d1000c27f42a105430a901ea8000843914f60cf82a385570ac21fd840907f8102a1ff440f014809921fd0407834a00001966310130f,
0x1026a04a827404de09a2133425f078607100dd01ae035306640c9c2300455088c110c219042b0b5816ac2d505a90b5002a404b808400fa019c02f8a7f0290132440087fd0ff41fe03fb07f40fe01fb8415081e10302054409080f101220182a487ab0694094421c00010872151c19f0a7b0aae158400006598c404c3cfdc8ec8,
0x11da09bf454100f114e000085370a1505f60ba053b035c08aa111821900970108019c3c1054c0ab0155c4fb017e09c01ff841104ec100620c42720800105013a8401082e026a1c80511813d09821fcc40685420ac205cc26d07fc10380000fdd0659261e087ca9788754dfaa2687698a8104e61130005836604a6135c3a18a4e,
0x114dc115450882e8012829d800309fd1502057449588cd13ec052452805480f5415302ac0a7e000210e453d833e0a8e155c00007d0032613b04018831027a13043f9880d02e613683fe081c03061390400082802fc13803ff0822031e13a8401082e0fd22a0053c07820a8415840001fba0cb318809878ec81d943b307670ed4,
0x10ac20000fdd06598c404c3c7640eca1d983b3876a0ed01da42a1400602e505bc0b2416382c6058a0b1016182c2091c11fc001093d1506277c2a6054e00007eeae69152f566caad154126fc566aa26941f46224cfc2a10538000201e212384ed02fb05d015300001fbab9a454bd44d283e4cfcaadcece8a8301e229c017d8002,
0x10896110c04a008600f200184fe85430a881c842a407aa0a9c22880dc880c03e820b400007d0032613b04018831027a13043f9880d02e613683fe081c03061390400082802fc13803ff0822031e13a8401082e0a84235c0e088100fe813240a40a82069407a041087e9150029f8000843914f60cf83c1054714f015302ac0557,
0x14cfe76761d5043d150c289c51780cc05e20bac07d047a0930125c0010a25034e06c0403880a0fdc1fc03c304be064e0cc821604330488093439e865e102600143fb01ce0b12133440b000a025405543fc097512e81f882688042008000fc01f003d0076089c11302250448088c09a815d081c103c4d487ca15080d981a98455,
0x113e00b2c1a5092c13ea1fa42470a2000042a1817d82e80f0415082a605580aae158426a816a00007ee832c930f043ea0f944d152f4cfe76745438a0d018c03e823d049703720350451080c090627c03f482cb0694276449609da14dc29c053606fb14a01e082a1054c0a9a15602ab856105d00000fdd0659261e087d44d152f,
0x10ffa070426f081002f21fd020c84c90e8a0d281138226044a0890111892c081e0524000092a09d8261c27504e409c013682608803100420003ff01e80ff81fcc418882e10502088410881c101a15082a207210a9815341b304d502d41f9c2ac05570ac200009890659261e7ee410fc5c6513454bd33f9d9c087621d4544047f,
0x112581fd052d0a5313a4203c3c105420ab0155c2b080003f741964987821f2a5e99fcece043d10e62a2851100ed01d211c424681b013b220203f48a8814a01e082a687e70ab0155c2b080003f741964987821f8b8ca268a97a67f3b3810ec54480fc141a126846881e201aa0b2416382c6058a0b1016182c2103e235c23f047f,
0x10198031817882eb01f403d027604ea095c12b427204e00940127c26d04c108f611e824c0497100620080fa08000ffc07a03fe07f303722288418882e105a20a041108211038203440607e91514000854487e7150e05a852805420a9815342a705580aae15841ba078200007ee832c930f043ea0f944d152f4cfe2a2c1a504c9,
0x1142410f421f034a09921fd040801c1150805202a385490f5622882ac05570ac206e440601f4105a13083f9880d06f613843ff08220fd220603fd04d702d22a2c1b3078200007ee832c930f043ea0f944d152f4df82a3040801c10fe8120c26482c90694003049605cd02921fa85068312022c0c0017f0107020c24a815d82b8,
0x1100620080fa08000ffc1ff03f981b9114420d0418882e105a20a0411081c101a20303f488180fce1fe854184d702c6277c0b48a8b0a8427a84220843108a28c839b0a50108c151c2a6054d0ab0155c2b083660f040000fdd0659261e087d41f289a2a5e2a342da800b14f001d403a007300e4096c12c825804ae095812a8254,
0x1043ea268a97267f10ea2a3c3fd03cf09ae277c0b480000cb24c3d44d462243ae99f85470980128209ac041007f0664111c2230a2a06b81c8053b08cd14462a303f8080a036011c40000a2201da03a43e8048d072e064c0c7818c0004060c0bf017b06f605cc1b7813d027213c027604ea127a139027004e109b4136c2608804,
0x14cfea0f84398a9215202a383a48a8d06cc29403c105580aae15840001fba0cb24c3c10fa83e51342a440e989a5102e1fa454780000cb24c3cfdc821f51344c48a97267f15200d2853d092c029224a827604ea09c8138026d04c11006200840007fe0ff81fcc418882e1050208840e080d0a8415840b50000262419649879fb9,
0x10a861510390804c009a10781180231083e0002c4d2642000a32a865c196032bc32d931e8a950e86096c1268244088410d83e7007400c801702a385570001626948ca8594cf86dfd41c82211d9a2a503a1825b049a091022104360f9c01cc031805b0000a46541ca85904440886c4d1b7f4cf83b2c54981e1134a2074000152e,
0x1067c0002d5b02218c411a887670ec81d943b307681fb915301ff026d081a02e6076c13e8453120c2a583f404bb0fe020243f489d5034c155c2b08000261e6dfdc9c0005195c32d0cab195c1954658065c0cb632bc088541ca8592a5a2a5c40204ef106406680fc829e08d400009879b7f044254b4439865984ee2a5848508af,
0x1034e11ac48180e801ca0388245048b0fa605742a207210a9a15602ab88530680130809c837109b605bc0bd839009d6063000007d0032613b04018831027a13043f9880d02e613683fe081c03061390400082802fc13803ff0822031e13a8401082e0a84000032cd89a261e7eec43a952f087698f854c809314f6114821c836f,
0x1153215342ac055700001f400c984ec100620c409e84c10fe620340b984da0ff820700c184e4100020a00bf04e00ffc20880c784ea100420b82a100000cb362689879fbb10ea54bc21d8a9a0fe028a84050334036011c40b00a2205ba123453507d502d2103c1f98225040a25d010081ff03fa07f01f7012a0f0c1fb84038329,
0x102fc13800c784ea0a8411ec1a004c20fe6203424c037109b61ff040e04a006fa13843ff0822095c000854d054c0ab0155c1c804eb100420b80000659b1344c3cfdd88752a5e98fc54d87f0097c202819a01b008e2288807880ed01d204d42468a290faa00e801c8038006e00d801a82220442088010f821e02d2102420507ca,
0x101580a20142809e01360944037806904f809d8049808f08ca119022d0459087410e422984520a8e15202a487aa0f560002d5b267e5136a46944c285e50cc088454e09ec0126284850b845200020c6018202c005ea2314466093a127a1f540b488cd0f94151c00007d0032613b04018831027a13040b984da030613904000828,
0x1b13498f942d995f195a087c54f800111762a7049d07d502d2151c2ac00000cb36ad89879fbb10ea54bc21ea91a5130a179433285b4cfc2a7845080e801ca031823d034009841fcc4068106020e127c1be84e10ffc208808b04ad072013ac401082e0000196487b1fbb10ea10f531f371f153a09d000587db0b4002280030297]

def cP_1 : List Nat := [
0x10a9c15602ab834009840dc426d837d09c20e4027580000fa0064c2760803106204f426087f3101a05cc26d07fc1038060c2720800105005f827007fe1044063c2750802105c15080000659b1344c3cfdd88752a5e2a80005865f0b2823403ea026b04d409a4133826604ca021004180820102111c22305490f541eac2ab8000,
0x132c22a84135844a0f4e020c53d80ac013c026c049808f08c8116421c845200022a7c0028589001425d40210040007e00f801e803b044e08981128224044610382078a9e05ba0c6018202c005ea003016e02d909182a743e9815d15360c4818002fe05e20bac15d82b8095c128024c047b00042a682a185440e42151c2a6054d,
0x1065211c43f30a2201e203b807680ec01d603a4246836809ae1fe840c8a2102d204a809a840f07dc1c8011382010a9a15602ab834009840dc426d8aa000001f400c984ec100620c409e84c10fe620340b984da0ff820700c184e4100020a00bf04e00ffc20880c784ea100420b82a100000cb36268fdd8875261e54b021d90e4,
0x1100620c409e84c10fe620340b984da0ff820700c184e4100020a00bf04e00ffc20880c784ea100420b82a100000cb36268fdd8875261ea46c55207fa1032135c51081690000196443a930f2a5c54b2311267e15461fb00de81ba036620300ec081b03c8208400008752a5c54b137e3c151544227c40387f00fdc12f83c30334,
0x108762a943f601ca039220583fc04d102ba1f28551836806bc123424500e901c4283406b80d508fc235c48784c90fe82040551014814462a8407d00f4092c000824c02f510b00dbc0ed817507aa15302a685580aae28c842981b31018076040d81e410420ce4261036a06d60dc426d837906fa13844238aa000001f400c984ec,
0x10580003016e02d90a8e15382ac055705700aec17f030006240002c4d291a4c7c657c656c40487950f48ec61d98878e2a983f601c9132e205840987f80fec1344266835e06aa122824280e20f34240806200c30184030005e8471036620300ec081b03c82084000065921ec7eec43a952e2a5899fd31e393a7234a9d487610e8,
0x103c820841a004c206e2136c1be84e1072013ac55000000fa0064c2760803106204f426087f3101a05cc26d07fc1038060c2720800105005f827007fe1044063c2750802105c150855200000cb36268fdd8875261e54b133f8aa704d611283d38083128402b004f009b0126023c037846408b2114821c8001153e0b7418c0304,
0x1087a2aa03f601ca039220583fc04d106bc123055302f105d62a7425704a0093011ec0010aa511ac235c002834c0668162426484be001405543fa07f012ea1f88408080a0084010001f803e007a00ec1138226044a0890111813502ba2a880a409c0081c103c4d487ca13ec150c2a207210a9815342ac0557036620300ec081b,
0x11042000043a952e2a5898f9dab8aa90fd807280e488160ff013441af048c153a057416e88cc1176000454e031806080b0049d093d095c128023d85470a9a15600d9880c03b0206c0f20821068013083f9880d06e2136c3fe081c06fa13843ff0822072013ac401082e06d02a8c0000659b56c7eec43a930f2a5ca468a96267e,
0x13f7621d4987952c4c7c2ab03fa081009922a880a400000cb221d4987952e2a591a8137e0aab1446052039004c914541fd03f80810101406e80d4813902de05ec27007fe104406302750802105c04f426087f3101a05cc26d07fc1038000032c8006262421d4987c5e026211a80a918aaa0fd807280e481b31018076040d81e4,
0x1141a058007302dd14d41228245835e09a21fe040b0aa902ba150842981b31018076040d81e410420d00261013906e2136c0b7817b09c01ff8411039009d606302750802105c04f426087f3101a05cc26d07fc103803b8078033408e2288807480ed01e212341b40aa30a9a00085540aa715482a802a605580aae000032cd89a,
0x1155623744668aac01e203c007700ed01d803ac074848d00042aa01b40aa3154e15302ac0557154000003e8019309d8200c418813d09821fcc406817309b41ff040e018309c82000414017e09c01ff8411018f09d4200841705421548000032cd89a3f7621d4987952c155a1fc04050a2a03581c805118aab0fd82aa81a6047e,
0x12a5c54b0a918aaf13d41fac1a80152025c132c26504bb0fec1fc01ad035906b00d5c0ae015b02b405640ac08131014133c26701c403581fe03f10720112220583928a23000026400ec81b512f61fb055101ba0a84150c39b0a50036620300ec081b03c820843f48a4f0000195ec4d1fba261c54b8a963c15155c11f81a600d0,
0x110421fa452780000caf6268fdd130e2a5c54b055889ea14660cbc09a04bc09761cd85280141028605140a300000cae7ee898739f93f547eb8fd81fb225fcb24455809ea14660cbc09a04bc09761fc040507c00352067c39b0a500282050c0a2814609880d081a20345068c13143fa0810155c1fa452780000caf6268fdd130e,
0x115681c8051181ac037a07640da880c10360000003087576aaf054a958ab313d42134426084b1094212439b0a5000007ee89888ab213d428cc1b1816809a613483fd08191442270040507f015602244000097b0fd82abc1a3034506880d080a301450286050426284c40fe8204055705420a861cd852801b31018076040d81e4,
0x1000224b02a10a171424151c2ab8000b134a26148d285e50cca49948ca67f4df82ad83ec816602c813483fd081903a62ad052801b71018076c40d81e7104207cc41687e9149e000032bdab63f7454b497f130026084c289862919261099f855a808d114a112c0008a9c142e28482a38000b56ca26148d285e50cca46533f289b,
0x115740234452844b00016ad948c8ed21da0087d44d8ab90016168014b8288050a094453d827e04f809d8049846508b410e821c845308a415243d58941128024fc2a38000b56ca26148d285e50cca16476826ff04422ae000502150420089c11302250448088c200040f0a881c84000589a4cfe9bf40018ab713d8024c4c50452,
0x1034c024c4ea845200022ae80000ab7156c15080fc88331282076c40d8940127e07cc4168a17036e203050905470aae079c4108000b13421d4a96a859523299fc55d89d104a6093421c000b14f60960126024b04920920123824600d0019421f0433086415243d585570001626944c28591d903b2876629191da099fd37e821f,
0x10f8e20ac40c88161026201c40087fa0ff01fd83f704e609a4133826504b6031205a00ae01540252000032b88752a5a4c3455e87fa09a420640b381d3156a2ad055d81bf10201fd02620a600aae294055901b71018076c40d81e7104207cc41687e9149e000032bd89a3f744c38a96a85925fc4c00982130a26182af021708a6,
0x11280079c410893f03e620b43f48a4f0a8e155c55f0ab10000195ec4d1fba261c54b942c92fe157e1fb41b3036406c6134c3fd081903a82aec3e381bf105620584098810100e20043fc07f60fe81fb827304ce0994131025b083e107a20f041d818802b6054c0a301280e6c29403f48a4f0000195ec4d1fba2a5aa1649858abe,
0x10f9227cc3d2073a125e069440983a2100e1fd83f704cb096c0d4437586e50dc01b5836986d00de8048c3f68abc06cc0d901b1836206c20d800b284d309a40f383fd081903a62ad055d81bf10200ef43fa04c414c01ea82a6054d0e6c29404510ab2076220341ee882207c220a01f387490ab020b80db880c157a25040ed881b,
0x10d9e1b280ab854d0e6c294040607e9149e000032bdcd23f7454b4fd51fae3f647ed097f8ac108e60adc001099208e8205805e07f80fd4133837986d20dd41b9036f86d50d9e1b280ab8abf035c0ea4405054c0a9a294040607e9149e1d242ac05571562000032bd89a3f744c38a9747fc158027e036602e805cc000850687ea,
0x102ce054809384c406641fac5300abf15820cbc197032d065604c4098012f025c12f051684bb0fe02b0055e81f903e6079c0ed81b71562151c2a485580f56155c39b0a501018206c410882d10661fcc40687e9149e2ac80000657b1347ee8987152e15841fb436306c80d92264840b07f80fd4133837986d20dd41b9036f86d5,
0x11018076c40d81e7104207cc41681f910662af43f48a4f0000195ec4d1fba261c54b542c0ac30016168014b825304a209f013402641166119421d04530892274455b0001039a2ad03e587410e802ae43e381d30e741ec00d28a12142e20ac40c8813100e06fc19808010ff41fd83f708100fda139826904ca096c1fd041d0187,
0x113a22ad800081cd15681f2c3a0874015721f1c0e9873a0f6006945090a17105620644098807037e0cc040087fa0fec1fb840807ed09cc134826504b60fe820e80c3816702a4049c26207eb14c02b04199032f065c0cb41958131026004bc09704bc145a12ec3f8080a035c151c2a485580f56155c39b0a500fe6203455901b7,
0x115882af85618abd0a8e15342ac055714a020303f48a4f15642b080000657b1347ee8987152d158a11c40010a2201e2124007680e913c207580e98ab4157615302a685580aae06dc40601db1036079c41081f3105a06c00d78000b13421d4a97952d50b2a464562000b0b400a5c129825104f809a013208b308ca10e82298449,
0x10a9815342ac055700016268fdd3c1654f4aa08a9610f221c51ff23ef3b3554aa43a856384ca02a81fd853008130d901cf42a60a5010181fa45278ab2028c000032bdcd23f744c38a97b9f93f6e76748718ac61490255c363836b06c61fa856086f30da41ba837206df0daa1b3c365034606880d0853004c509881fd040801bf,
0x103e820b43f48a4f158a05185630ac20ab0155c0000657b1347ee8987285973f27ea8fd71fb03f6443c8fdb9d9d4dfa4bf856508d000ce022c04504460864112c0005ab650b2a26d42d8ec81d943b3010f8ac9000222ec54e054700016ad944da8985234a179433285b4cfc2b2044f8116020e04183ca84ad093e00082358903,
0x1087211480008ac9067628c4564093f1280250416e831806080bd4160048c095c128024c047b000411c407280c0158e0ba03e481d5039c069c40c8816100e06c03fd07f80fec1fb840504d909a4133826504b60fe01bc80b8816802b805500948ab014c015082a3854c14a0206c45107fc10382ac80dc880c03d020840f60827,
0x1159a1fac37d06f30df21bd837b86f40df01bd45280ab200017348fdd130e21e62b303f506d20dd41b9036f86d50d9e1b285650ac606902160487089c06940d181a283440684131426207f4102007082a685580aae29403f48a4f156421585610ac50000195ec4d1fba261ca16548c3c14159629ec02e842e013c024c52d8459,
0x1566a43bc56707eb02b605a00b38166099c13483fc07fa102c20640e701d5145e24f423709f10dac1b6036b80b610b01fa816582f105d603d02418498092e000823f0a0d0a9a29404510ab210ac06e44060acc11ae234c0f4082111ac07d041687e9149e15302ac00000caf6ad8fdd130e2a5e54b148c2b3521c44bf887810ee,
0x1149e15302ac00000caf6ad8fdd130e2a5e54b148c2b3521c42b403f704b6100e04a444f07eb01a002d837606ee0dda1bbc37806eb01ac02e45668a5015642b3046b88d303d0208446b01f4105a2b380dc880c0fd2293c2a605580000195ed5b1fba261c54bca962918566a438897f0acf000411f823d00d50198000021f2ab4,
0x1b9a47ee8987152f25fcacd4985130c26004c10984130215a41fac0b309e409a41fe840c815402a605480a8014f029a0754265048d0fec0008409847a0e7a03a40630a50156406e440607e9149e000032b843e3f744c38a9790e315a21fa837506d50d942b3c2a68a501598235c46981e8104223580fa082d159c06e440607e9,
0x110361fa452780000caf7348fdd10f221c4acd487610e621d043b89818ad30fda1b6836e06db0dba1b7851d846e016c1fa807a049708f607540d800021032202823f07fa0fe0283426904bb0ddc20d80b301310fd624442a6873614a022885590acc15a2235c46981e8104223580fa082d159c06e440607e9149e15300000657,
0x104a6288c00585a004540a5c144028504a229ec13e02760126105855c046508b410e821c845308a400000008ab7156c2ae455a093f142425004a08a1705d00c8018c030405ea0b002a105470a921eac2ab8000b134a16548cc404890d0f2a1e94492880e767456a00020f2a11f83fb0a0d0fd4132837606d7029e15302a68a50,
0x105fc0bac15d87c90ebe1e5424184b5095c1298250049808f607540d380021032201c23f07fa0fec1fb850684d2099412d8377816702a4049c2a1054d14a0206c45101ec104e07e84198acc11ae234c0f4082111ac07d04168ace037220303f48a4f15a02b442a60558158a2b082ab80000caf6268fdd130e50b2acd49848ad5,
0x1092e11f807a0a0d0fd41bac36b054c0a9a29400005cd23f74acd887910e2566a43b087310e821dc4c0456b800208fc1e543fb0a0d0fd4132837686d802a015302a68a5010361fa452780000caf7348fdd10f221c4acd487610e621d043b89828ad600001f044fb8ab7062c0c2018102f3057c0b2449e88d515a81fa81628300,
0x13f744c3942c92fe566a2b6456a0a3b096a12b8250049808f6276800100ed0ea22b1c0ea81b0034e206440508070ff41fd83f807ee09a4132825d84b602d0055009a01290a9a206c45101e8104207d041681fa10662b3056701b910181fa45278ad015a215302ac0ac51584155c0000657b1347ee89872859566a4c3456c0002,
0x10ebe1e5425a84ae095a128024c049708f607380d381b000042058403880a08fc1fe03fb07ee0fe0283050684ce099412d851686f002b6054c0940ad215b02b5c56b0ad515a62b4056708d611a6235c2a68a50103622883f9880d037220300f4082103e820b40fd08330fd2293c5628acc15a22b082a605580aae000032bd89a,
0x1099c132825b07f002d005700aa012915601fac1a3034506880d080a301450288050c0a10141098a13103fa0acb1020070456c8a501036228855901b9101807a041081f4105a07e841987e9149e2b145660ad1158415302ac05570000195ec4d1fba261ca16497f0ada15a827684f38a2f01ca26e83b202f105d60ae05638476,
0x103601fd023888100004070424f88d3020c07a041087e9149e000032b843e3f744c38a9792fe6e38439c56e07ea0da41ba837206df0daa1b3c365054d14a00002e691fba21e4438897f8adb15a828bc25a84ae0940126023d82e50004276823885ca01da030056381d5039c069c40c8816100e06c03fd07f80fec1fb840504d2,
0x1022c03d0256849700042b7456e0a0c141a153445101f4105a1fa45278adb15a2153056600000caf7348fdd130e2a5e43a887710f021d82b785300134098828b425d87f40fe0204040501c1036011f82388a500fe620343f48a4f1564000032b9fba261c54bc97f37dc6e3810ec56e8ab00fe00d181a283440684202826284c4,
0x115b81bb037706ed0dde1bc037580d6018629403f48a4f15642b6c568854c15982b7c0000657b9a47ee8987152f21d443c4570018909cc1fac4008146028a20ac26201f00fe8129c40800020382127c37186e20dc21b8046b8110020e294055901e810421fa45278adb15a2153056600000caf7348fdd130e2a5e43b456f87ea,
0x1147611d80005cd2566c438942c10ee6e3810f62022a55566aaadd53a8ae3056c28bc23b01ce0360205840507f80fe0133825d815c0268000032b88752a5ea161b8e1d8c087aa954ecc130d15c4000823d0add01aa033006101b910181fa452780000cae10f8fdd130e2a5e4bf88778ae10fdc12d84038129113c1fac06900d0,
0x102a42b4856801c110201fd02620a600a8e15243d5873610362ac842b01ec104e2b1436b86d80dac294023d81b9101812800f40821095c07d041684b503f420cc57102f10930228823700b600042b7450685ca15bc28305708adf0a9a2b6856d8ad10a982b302ac055715841fa452780000caf6268fdd130e21e04c2857202b6,
0x1158415302ac05570000195ec4d1fba261c43c057285a0001623c814b80ac05100a1404d825100d209f013b008f04a62290232846408b4116421d043908a611484e88001156c2ae455a0a12142e0cc0174032006300c1017a82c00fda2160199032f065c1e600d80ae30f92075440c87fa0fec1348265083a107220e00be0167,
0x103d8209c0fd08330fd2293c0000657b1347ee8a9790f115ce02d857000b915ca2b082ac05570000195ec4d1fba261c2b984f38ae308ec07040d8081010141fd03f804c4145a0518572046e093011ec0010add15b817342e605c901da039405b0a0c141a2b782a688a20fe620340dc880c0fd2293c56d0adf15c22b6c5688acc,
0x10996132825e04bb099e133826984d210021ff43f707f60fe01fe03fd082b103e201c409880a102c20640f801e2034e07200d801ce03aa12cc2520496094e1268235848508e212282468002092e17842f005df0bbc17742ee01210222042c08100fa01e0039c07000c3017215082a608a20ab0155c3f9880d0ffc20883c10ae6,
0x10000195ec4d1fba2a5edbf1b8e043b15d2283423f0ace0a9815340005cd2556843c087110ec087643c959a8ae811fe254c1bd84df02fc2a5401283fb0e84227451e032006120bd416588d1059211fc0e08216005c009c408040208021fd000004c402921f281938a4e02540d4c199013506b805741b3016909cc137025b84b6,
0x1016c000032bd89a3f7454bdb7e371c15d4094c21c000b00d20960126024b049209201238246135e10f82198001148222743a1834a0290131426207f41020070457400c5064e04a81990135096e12d825e04bb0fdc1fc0403880a034e06c023584710a8e15242ac07ab0aae1fcc406878215cc06e440607e9149e2b9c05900c1,
0x13f7254bc21d9d9d50b02bb037e07900bce240808382bb0570127c23d854d14a01e0806100000caf7348fdd130f5568a9e887810e221d4dc7421e8aeb0df81e402f387ea022c041807a02bb05700330256849f092e11ec23d000215d203042a6054d14a022882ac05570f042b980dc880c03d020840fa082d0fd2293c57380b2,
0x107e81644113820107f62744511854300002adc2a10000b134987537ea67f4cf82bb8215019a04781f9451188f514b601a421c80011572285c2a105470aae201041a07e9149e2ac83c10ae60000195ec4d1fba26044c10985130c50724bf937ea91951360014768285951302bb440501b00fe011c825e02b60664000032b8875,
0x10a840cf83bf813d15dc05a426907fa103207542468a22029013103fa08100382235c3f500bb018402f405f00bf0a9a04a825b07ee100e069c235800215d62ba805b00b215ce07a041081b9101815302ac05570fe620343f48a4f0f042b980000657b1347ee8a97b6fc3b3a2bbc002803f00240044008001c08220fc4012801f,
0x10fdc201c0d3846b00042bac06100bf017c02f457500b6016415302a685580aae1fcc406878215cc06e440601e810421fa45278ae70000195ec4d1fba2a5edbf0578800114b629082a38000b56ca0e548ca89b4cfaa26142c8af015da284857603040a8e0490092812802520c9c25b8adb093c041c1a504c506cc134c0000ab7,
0x1102c122c3fc02dc099c05785270136056826e015982b208e406c040507f009780cc85780aef067c1dfc09e8aee06cc05a41a5014809cc137026504d309a4131426208010ffa1fd83fd07f41056207c4098819102007c00f101c803aa0704253849a090a123446b85d20b9e044008000de132828883f500bb064e04a825b84b6,
0x110141fc025e03320f041fa452780000caf7348fdd130f2a5e43c087610ee50b0767457a02be0eca2950237047b000411c45060af213281f9c2a6054d0ab002cc05b80b800016ad959b2ab4550443c1b7ea85854eaa26d48c8ed24cfa7670579800108682ae4030887e1490151c0005ab650b0a26d48c8ed23b38438c57901ce,
0x10caf7348fdd1fb92a5e43c1b7e930054ea7672311a91821c42bd851d09ed05e61d9452a046e093000082388a2314182bcc5790a170a84151c2a6054d14a002dc4ca07e7016602e02ac055700016268fdd2b362a5eaad154110f06dfa9bf4980285854ea767144c289b8c46a46457a80c6144e11e80010aec0a9806e440601b0,
0x1010c01845240af615ea0d9c2a388a2037220300fa082d028205240d8080a0fe012f019907820fd2293c57a00b8016e2bc45738ae60ab0155c0000657b1347ee8a97a6fd50b0a26144d8af713da11b849e800213e22ba04e8054c0a9a294045101b9101807d041680b3016a02dc05c07e7038220403fa04c506941fa45278000,
0x1016602d405b80b8036020283f804bc06641f9c0000657b9a421d559b1fb92a5e43c1b7ea6fd50b0767155b8afa127a00084f88ae8038220403fa04c5069407d041687e715f006e4406054c0000195ee690875566c7ee4a9790f021d8767155bb7dc52302be4001048d08f403a40630000087caad155b90e315f000042258434,
0x1149027b40d388070fdc12d80950aee027a1dfc19f0af702d227d426984d20ff420640ea8afa0fce2bd00d8080a0fe012f0199054714a022882ac05570fe620343f48a4f0f042b9c05b80b815e205040a48ae60000195ec4d1fba2a5e9bf542c0afb15c627cc237047b000411c457c89d014182be02a6054d037220300f40821,
0x1028605180a480000cae00196af1310261e7ee537e92fe26180014110c1e836fe2bf4006086910d42198433886510d0002c13f826704c40984130025f04bc115c22504450002025003f807915922704524087310e221ac2a385490f5615382df855800016ad942c90e33b2ca0ed44da85b507e767057e0001089610d00430061,
0x115cc06e440607e9149e2bec0000657b1347ee8a97a6fd21c62c003f70807096e226c1938a500fd2293c3c100000cae7ee8987843b2a54767541c0aff000a011c00e0038006e00d820e0025003e0fd02060591045e0fec4e888c21446150c0000ab70a840002c4d26fd4cfe98fd311a67c15fc10a811e019a14461f941298142,
0x100c40194033806800016ad9a80b5431602276c043005e00d0019c0328062089610ac219000114b62bfc57f02c015f80dd00bc835c02ba137426e04cf099c1ff43fc0169038a207c40b09f509a40d4c0aa81e2039c0aec3fd04cb09941268245047910321fd800101d5102611e857c073d01f8038806305470a9815602ab8782,
0x10f541eac2a685580166075440c87fa09a60d9822587820fd2293c0000657b56c7ee8987952f6dfa438933e821f1d903b287660ece1da43b50db81b7236e86dd8dbd1b7c6a843b1858187cd05541bf02a3855814a0201c3f704b7064e1e083f48a4f0000195ed5b1fba261e54bdaa12ab7507107a63ef1d9d1604276c0458086,
0x1104207b041381f4105a02cc05a80b701700cf83bf813d0fe620343f48a4f0f04000032bdab63f744c3ca9790f06dfaa164871267d043e2c144e80af90fce15340000657b9a421d559b1fb92a5e43c087210e821d843b88712ab75230767058207a511041f9c58107f609960d4c221825300f8002c21580060f7422d02a40549,
0x103d020840fa082d03f420cc3f48a4f057e000032bd89a3f7454bd42ca89804427675bee375e556e2c183e482e80df82c1021f07f604b0132c005835304a6110c21c007900d22c0c0ea88190ff4134c1b3044b1602093012582490490091c123006800ce0194032006300c410cc21905490f56294040d88a20ab006e440601e8,
0x115fe124452d82e913ea1fe840c81d5160c26e84e806fc0a9815342ac0a50016602d405b80b8036a203019f077f027a1fcc40687e9149e1e080008b0516002bec5788ae715cc151c2ab80000caf6268fdd152f4dfa99f4ece8b0713e22a7056a031806080bd425a84ae0940126000102e8091a27682a608a20ab0155c3c10ae6,
0x121d6df7155b0b0a088401c812c094200161df41260248048e09182a4806f08721df83d5825108740002d5b285951300884dbf0ed01da8a4647671b7650b706a4584800b0498092021b059400c40a20142894208b425002a385490f5601bc21c825108740002d5b285951300884dbf0ed01da83b38dbb0ecc50b6a1785840002,
0x101702bc457d8b000000195ec4d1fba2a5e9bf533e8b0b14f6018c031043616120d7026787f8102c07383bf048a04800174001042f085c27c44f70a5b02d227d426907fa103207543d5854c1144156021c825104a610e819f077f027a1fcc40687e9149e1e080728882111a000032bdab63f744c3ca97a6fd50b299f41109d9c,
0x1156e0aec49e849808f6000817282e3091a27682a1054c0a9c15602ab8000b134acd955a2a824dfb013cece1d8a6ebc7630ec71d903b24aadc586000c057c0aec23d800205ca0b8c24689da161417342e605cb137626e84e807a513281f9c5838001160a151c2a6054d0a9c15602ab8ae6037220303f48a4f15ce02cc05a80b7,
0x10ab0155c0000657b1347ee8a97a6fd556c2c3840507f0036012ec2388135000427444f7016909a41fe840c81d5161817342e605cb137626e850607a513281f9c2a6054d114415602ab8ae6037220300fa082d0fd2293c57380b3016e02e05788b000454288c58585420000195ec4d1fba2a5e9bf4ece0b0d082c0bcc000000c,
0x100040ba024689da161c26e84e806fc161a2c0057d85470a9815342ac055714a01e0857301b910181fa45278ae7016602d405b80b815e2000032bd89a3f7454bd37e8b0f101406c03f804710976000809a849113a20ba40b489f509a41fe840c81d50a981fa45278b0b14181bf0586878214a02b9805c00b715e22b9c580054d,
0x115ce02cc05a80b701702bc40a00147038206f440807f40988052057307e9149e2c3c0000657b1347ee8a979d9d16220b2c56a0483096a12b8250049808f600084ed0ae81374274057c054c0a9a15602ab8000b134acd955a2a7a5504ad0887810e421d043b08772b353b3a43c942caab716202c04225843200022c18160047b,
0x102aa054c3fe87f80872132840f8816142e2bc000087f603c40738160092c10261268245047905961cf407e00e2018c11fc57f8ae800041244174836602d205940b204d309a41fe840c81d516202bd037e05420a8e15203d5054c14a022882ac05570ff820703ff0822100820d05590782037220300f4082103e820b40fd0833,
0x113281f9c58880b301702bc457385580aae05a4269036609a61e0857300000caf6268fdd152f59a610ec589037b09be23ac0bf0962049a09100220228086c1f3820a841600d001800b9823b042c016000304d908541008214807600ea0dbc000019a088428f03e50a4915282a4c3f2825b02f20d700ae88f509b8133c2670069,
0x100042c480b484d20ff420640ea854c11442b980dc880c03d020840fa082d0fd2293c57887e7162215602ab80000caf6268fdd152f556c2c4c00007cf0802055433a866f11ce132843487f60018204c16482c7058c0b1416202c31382292039e847f15d015083d5054c0a9c06e440600b7038220403fa04c402902c3c3f48a4f,
0x1076220341ee882207c220a01f3882e07d21d2458a08310fd2293c3f385580aae000032bd89a3f74767021e8b15137a0b2415d848308f6000857409d015f02c4c3f38b11038220403fa04c402902c3c05c00b7016a02cc5788ae7037215302a685580aae20303f48a4f15cc000032bd89a3f7454bc58a09e5018c27b8237047a,
0x11036079041083b1101a0002c4d08752a5c875c879043b21c4dbf458b07d102aa04a800004ca096c1f403fb07ee06340c58184030205e60af81e203a20018122023705cd01ba02d83f50312022c0c0017f0107020c0bc417580fa01e80aec15c00cc018c12c825704ad094c128024f8498092e11ec23d05420a9a15384510ae6,
0x108e226e850605420a9a20b40d9880c03b0206c0f20821037420401de0ae8076220342ac05570001626843a952e43ae43c821d90e221e043b087210ee162e2aec55a01bf035c07cc0f381db036e26203f60ab3101406e840c83a810200f3823883bc091a283057409ba017202e005b80b30a8415342ac0557105a06cc40601d8,
0x121d82c6455a8abb157c06fc0d70abd1014227c1d400c9019011c437386e90dca03300610b1714a02b6c05b0807074211ac58b081007782ba03f38002162a15301d8880d0e922c502ac05570fd2293c0000657b1347ee8ece10e221e043b08720b1815762ad00df81ae03e6079c0ed81b713101fb0559881910140f381d4048d,
0x1105a0002d5b08752a5cdd7955b3c15772e99f858d0149125e131855a034b157606fc0d701f303ce076c0db87ec156620281d40471017a2c600dd08100fea0ef05740542105a06cc40601d810360790410878215cc0ec44068807074211ac58b07e700042c542a60749162815602ab87e9149e000032bd89a3f74767087110f0,
0x108d602d858b07e71636000858a854c0e92156058a078215cc1fa452785570000195ec4d1fba3b38438858e0367131013504cb816a163420643fd881310200f381e183bc091a121446b80ee01bc15302ac03dd1044000032bdab610ea4c3cfdc952e43ae10ec8768b1b156806fc0f981e703b606dc4f08a210ab0203040d8821,
0x1039e000043a952e772eecdca960b1e14421ce84cc01cf102620641e183ce090a292057c00d91638000858a85470a9820301d88749162815602ab880d0fd2293c0000657b1347ee8ece0b1d0f8e20ac40c88161026227c1f183ce07900f0c1d404a7091a122824280d201a20340238811101e0039c07000d601862c6440383a1,
0x10fd8288458f81cf10321fec1e701b31018076040d81e41042000032bdab610ea4c3cfdc952e43ae767421daab6164013143fa034a10202ad058d016a091e1350174836703a607cc0f381db036e203040d8821105a000032bdab610ea4c3cfdc952e3b3a10ed55b2cd2772e54b458f89970fd828840d9880c03b0206c0f20821,
0x1508ea26ca968b2215a80c7c18b830305e80afc0d701bf03f207cc0f381db036e2700405081007500ef00b4847115d0134851100f001da1fe8247048d15f00f3c5900b1b0a981534406081b104220b441983b10e922c5040687e9149e1bf058e87820ab0155c5280ae60000195ec4d1fba08762c8425d87f0026a20280d689c0,
0x1096c1fb81d1046e016c055426507f60788122006e87ea01e8033007d04971144041808b04ad07ce20b8083849f07ba208837e0b1d0f042940063047a076220342a68002164215303a48b140ab0155c57305420fd2293c0000657b1347eea41f8b23099e0d703fc01cd102c1f1c0f781c7034c0750000065710ea7ee541ca83b,
0x100042c8437e0b1d07ce0f741d8874916281e0857308a2105c208840687e9149e29402a1054c0a9a15602ab80000caf6268fdd0b2416202b8c1de03a8102020280dd09c00fd82c881b3016909a613481e707fa036620300ec081b03c820841f5883408f6283019384b706a6132c1c404e710020f90254810f12f600003e8812a,
0x110ea7ee4a96bc14164c1fd040804c5037e0d2855a01f303ce076c0db8a2102d4135040c87fb1018206c410882d06ce000032bdab610ea4c3cfdca89b2a5d20f859282e9092226201e78819164625ec00007d102aa04a826504b60fec1fb81e203a2091011b806e80b60fd40458083810601f403d006600c6095a127c24b847a,
0x11652002c2da85b10b5e2c203bf024000ba0a201428251085e10b857e845a0874000455c8a120a8415243d5884f142e151c2ab80000caf62696af130f3f72a26c97f130c50b2001537ea91950b6a26141c285e16501fc040504bc035c0cc855d81bf164c000032bd89a10ea7ee533f952d164e13141a507f4038020400000657,
0x10f700a18005877d0a921df83d58000b56ca16548ca85f36fc08847631b7a1d9c6dd8dbc1b7c36e46dc05960b010fb610d8139824c0a8e0002d5b289b50b20884dbe8b2b161216981250b2904a210e80005ab650b2a46542da89836fc08847671b7636f22ca800585b50b6616c42d805af0a921eac0005ab636fc6de8dbb0ed5,
0x103c820844020834109e000032bd89a10ea4c3cfdca89b2a5c2cc00458ab908960002d5b289b52323b4810f8b2f00e411083db825516581df45968b2b16541df8120005d04a201a4217842e087410e43d58000b56ca26d42ca91950b6a26141c285f36fc0884597077a0b2c16503d50000b56c3b187670ecc36e22cb404d045b,
0x1071e07d0598082d1648151c2ab80000caf626843a930f3f72a26c1108b31165c2bf421d0001165e2ca05780a17067c1dfc09e89d106b80d280a404cf098a13103fc07f4102c20400e481ba00001fb04d481ad066404d425e04bb0fe020284e00b2702d205a00b104d20ff42c942a105430a8e155c0d9880c0fe620340ec081b,
0x10fe80d2826209ec029027d80c9018e030405c809e029b05320a4013f028c04a6002c2d00a98052e024c13e027605100a1404f025100de119c232845f08a4114c54e045a08b210e821c85490f560cf819f81b910180e0c1c201ec104e0e501ca81f710601cfc1b7837003ba206c3a0037b06f807a04108741064e0ca844d038e,
0x150b2087c59a04bb0fe004d440501ad138026200ea8819164e1fe84ef84d306d20d985990b240000195ec4d0875261e7ee459988b4011a0228043042b0896000459887410e801cfc193838e06f60dbc195038f06f80dc044d01f403d0077459805470aae2c9040d8821105a000032bd89a10ea4c3cfdca89b16640704408034d,
0x1035a0cd009a812e097828b425d87f0101427002a105430a881c842a387aa0f5615302a685580aae2c900d9880c0fe620340ec081b0ff820700f208210ffc2088401082e108e2ccc0b1016402ca05980b3816802d605a80000657b13421d4987a89a2a5c99fca960b35157401d803a007300e410f4000589a4cfe9bf544c2919,
0x1085c09b4043825304a22904227044d0874000459a0045008808a03900415082c05cc26c8371142e125c15b02cb01e811d824187ea1444283416000ce08f611e8567000201e003b807680ec01d603a43bd848e13b42744174036802ba052042c04d3099c243826203cd0ff41fe03fa0819102c20400e781c9037400003f609a9,
0x187882cdc50600ce019811d823d000201e003b824709da056c0ba02a68af80a980002e69289a556ea16153aa67d5568767459b040c006a0884002800a009208b420d041b12c022bc11c8055046208c0026804c084e109820f841e031e05f827484df07200df425704a006300c102320a120ce802b4453077d16521df8120042f,
0x13b1c7640ec91d963b3010f459c847b057c00084dc048d0b9c03b82a60000b9a4aadd33eaab43b387630ec91d963b3043b459c02e51370173c4ed0991138a288806180c0017a0aec066047608f611e800102b508e40ab02a68b24108e2ccc57c054c0fce15602ab80000caf626843a930f2a5c99fd55b95224c7aa9d555a1d9c,
0x10ff420640e98b351648000032bd89a10ea4c3d44d152e4cfe3b307640eca52322ce821c025314f62490445048301da271450689da0bc00b8c163000c057c0ae0066047b08f415342a701b710182be02a607e7167015602ab8000b1347eec43aa67f2a5a54a810faab71d983b207653c151da109a4767267d556898fcece1d8c,
0x116720acc15902b0055e0ab81568b370fce2cd857c08b70ef61fe04e88816066804d40e604bc097611183f808d0028c05044050075029206b80dd043e087a284850b8ab6157607002a6054d0ab01fcc406816202c805940b3016702d005ac0b501d2000226280f9882d03ce20840db880c03b6206c0fc88330a8e155c1b404d3,
0x11666211c0a08146029013100000657b13421d4987a89a4cfe54b56a8a858167a283424185e0058c003015f02b808f6000859d8b3805660ac815802af055c0ab42a6854e15f02b382a607e70001734955bab354cfaaad0ece43c5167803c0574048d15f015300005cd2556eacd555a10f221d810ec59d8a2201da11c42468002,
0x110ea54b410faab71d983b207650ece1da43b50ece10e221dc10f4ecc8b3e05ca2ce02e905cf13b41fa851100c3018002fc05f00bd057611d823d800208e42cf03f38ace166c2be03bd89d1066804d425e04bb0fe020280d7054c0a9a15602ab87f3101a05880b2016502cc059c0b4016b02d40da026987fa1032074c592090e,
0x1167015342a707e715f02b382a602b116780aec15f047b0001734955bab353b3899f555a043d3b307648ec60b4000180b1016182ac05620000ecf1d9c87887658ecd1d983b2476322428b3f103e07843fe845509ba02501bb0006093a21fc07e89ba01dc27682f102f905ca15203d5054c0a9a2c903f385580aae000032bd89a,
0x126184c40a96821f556e3b307640eca566a4c009850ece1da43b50ece267d1686283424185df0ba40b145a00b3e0a9a2d045670af80a981f9c2ac05570000195ec4d08752a5a087d55b8ecc1d903b2959a8ece1da43b50ece267d556810f45a109bb0bb8173c2e08000b9a443c887110ee3b1a2d0446885de0bba28342418b3f,
0x10caf626843a930f513454b933f8ecc1d903b285a280050cc6199832f066100381644012801f049a26041fa0a2307f627442a187aa0aae000055b85420001626944d267f5234a17943329261d909bf542cc1a94cf82d100770b3b091a00085a1077b0a982c903f9880d0fce15602ab80000caf626843a92fe26044c109831308,
0x1141a0338241847a000403c0077048e13b40b2c1740ace15f02d0c3bd8b4400d0019c032843308642cf40a401460282243826207f4102006fc59d054c0a9a15603f9880d108e2ccc0b1016402ca05980b3816802d605a8000898a03e620b40f38821036e20300ed881b03f220cc2a3855706d0134c3fd081903a62cd45920000,
0x110ea4c3d44d152e4cfe2d2040807f4037e2cf421e894100e400044c501f3105a079c41081b71018076c40d81f91066151c2ab80000caf626843a930f513499fca968ec9168e20403fa01bf167a10f44a00073000226280f9882d03ce20840db880c03b6206c0fc88330a8e155c0000657b13421d4987a89a4cfe54b47658b46,
0x10fce15300005cd25568acd95412b3521d899f955b9d9c16961fd0408090e0382000032b88753f6c7ee0a97ab34169428840e988190ff413480b48b480001626843a930f0caea268a970b4910201fd00df8b3d087a24fc03a0b45168e2d18000898a03f207cc0f381db036e2cd42a385571018206c410882d1066000032bd89a,
0x101e012384ed0af80a9a2b3846b854c0ab0155c000589a261eaad159b2a7a5674aa095612b42566a99fcecec406556e2d3424b80f4000422e8078048e13b40ba05a58af803aa20643fd04d202d215340ee881b159c06e440608d711a607a041088d603e820b42a600000caf734843a930f513454bd59aa67e1698000859d893d,
0x110ac2d242ac05571648203040d8821104e20b44180833108e2ccc0000657b13421d4987a89a169e1fe840c84d303aa0da000006573f7621d4a97aab6169c120c16580d7156c27d80c10192031c05c809e01080218047c08d80fb019c26e8190031806080bd407a02c0096a12c425704ad094a128024f8498092e11ec23d0002,
0x1019c12e05780aee02560ad815500ba0596035c239046c08d62cec23f847e06542c9057c054c0ab0155c0000657b13520f0987a89b4cfe875955a2a55566aaadc8762a753b3a10ec5a887f00978202819a01b00000195cfdd88752a5ea9d05a80b4d05d021600e981d6169c05ac0b50b4c169407e80fb81f403d807a00ee81b9,
0x143acaad159b2a7a5674aa095612b4254aaacd555baa753b3a2d4c4fb00d7032406380c101720278120c08f811b0218042007d80ce05962c4056a0ace11ae23582a605580aae11e823d8498093e128025684ae096a03d007d049700016268987a67f5568acd953d2a825684acd555b9d9d880e10f5bf1376a50b22d483f78750,
0x103d807a00ee81b910ae15302ac055716482030406881b1042209c41688301066211c5998b4f0000195ec4d0875261e99fca978b54000026a43e800c4023e046c086010801f603385060ae316a403e825884ad094a127c24b847b08f400085a882e90a84150c2a68ace11ae2be02a605580aae000032bd89a90784c3d44da67f,
0x10a840002c4d267f4dfc99f137e8b5604542c3051182c90906173415f09d00fd426e84de80fa01e8125c2a1054d05700aec23d8b410fce2be056708d711a60bf825008d60a9815602ab8312095c0002c4d043d556eacd555a1d9c54f4aa0959b0b55147611ec0010b3b0fce2d4c5a80af811ae2b385a70b4a113407e80fb81f4,
0x114f6002c14b80ac05100a1404d8093011e09f013b046508c8116822c8a1208a4114c0f981e703b6151c2a487ab103620844168000b56c21d548c82216a806de8dbf152d16b02ad80df81f903e6079c0ed81b7154420403fa04c40290203040d8821105a20cc5aa00000caf626843a930f4cfe9bf05ab8416045400005118ab7,
0x105e605cc5ab02be1648000032bd89a5aa44c3d33fa6fd087b1010ecd8b5b1418030c00010f621c443b887910ec6e3a2d6802e842e11662bc049f894012820f981ed83d5074e202842c09c016b0094c1288069087410e40008b2f142e04f82a3881c104420b80005ab610ea7ee144da67f2a5c767133eb9795232a2605ac85a0,
0x1087aacd487110ee21e443c0ec78b5e0906283416309b800180c545ae054d0a9c2d043f38000b9a410f555bab3521c443b8ec51d963b3476708782a833b247640ec70b5d01dc27684de82e50228003025783140a9815385a087e70001734821eaab721c443b8ec51d963b3476708782a833b247640ec743d216b80dc424c04d9,
0x10342068040c08171028203c40708091010201840282e40922214c4f085470f5426503f380ef01d412402a5049306980e402570314110422342ab8541082426e41b40000087a7668ece2ab621c47eec8780ed256691880eca952e21d71a884398b600fd222884ec8000b9a4aad959b9fba16be283424185d0058615340005cd2,
0x10aae150420909b906d012081a60000087a7668ece2ab63b304388fddaa55890c43c1bee0ed256691880eca8b61128421e85248a9312d824fc0db865603e6253451b882c14c005a40b4016702cc05940b201621004000426484d7134e26982758a420fd006b80e601bf034a13143f603cc0ff407441de07f40fe006a43f701a2,
0x10a822d84209033f138a11b84de80bc018202e005b047c13b803281778483058c00302e505c90b9617342e6054e0a96034c000043d3b347670ecc371c21e443c087b10e421d67658fdd8b621634204040c87f40ff4131426987e8131a1fa45b00370093203dc3d2890b0fa40c0015282df05c8124407504900a9a1f9c2a50493,
0x11d983b208728b660e920ea00d8080910101fa45b20000b9a4a9d155a9fba16ca1d241d881b9101a20300005cd2556a7ee843a8b64105c0f9c3f4874913b22d88257090b06280c0016309bd001802f0060854e01a617242e505cb0b9817342a580b8016c000021e9d9a3b387661b8e10f221e043d887210eb3b2c2d8c2ab8951,
0x1142e151c2ab800021ececdc879589a2a5aa26d41ca91950b676708710221513099f0dbf8eca1d983b2087810ec1d9c2da0577027404b609103ed84420f9c022c03b08b41284285c2a385570001626944da8395232a16c110a8984cf83b18dbf8eca1d983b207670ed416ce250843f887711140002d5b285b3b38a2607690eca,
0x1111c22344478b6716d22d984ce094414922a5054988f50e74285c57801b60a96000452105470aae000087b3b3721e4765ac4d1d922a5aa26d41ca91950b6a164ece10e251302da84e8827404b609343ed8442086c022803a80650a8e155c000589a5136a46542c82214cf86dfc7678b6913560198447806816ce1ce80db0b66,
0x1103028b43f9880b0fe020243f4880c10a6000021f152d772ab258987375e87971210fdd865916d81d0c1268244086c1f3846f8067116826c80370070087609480008a42034a20140d7080803a6205c0df880e0fd220300db85470aae0002c4d152d51323b207660eca1d9c99f0dbf8ec616d62d0446885e0112017782ee87ea,
0x10fd612340a68129028a05100a1814202820da026504b60988134c3f40b6c10a61fb840307f4101e1fd840907fa103028b43f9880b0fe020243ff082003ce1fa44060000087c54b5dcaa85f261cdd7a1e5c4843f762db4519814102d0059426484d706980da023f848d000412800be037d0272138027084c1129a1fd040787fa,
0x116de27484ec854c0a9a1fa44060000b9a4ee5487810f289087670fdd0b70141a035406a048314d007043a48b6e0a9a203855909d90fd220300005cd2772a43c087944843b387ee821e8b6f141a03502418ace15f00ef01d8854c0a9a203c40587e910180002e693b9521e043ca2422ab7087a875c5b7037d09be12800bf8002,
0x1556e43888758b7201801e940598af808e211ac1b403340652135c25f078602d004d00948a33029005140a1814102720d0026484c1098425343f404c5069811fc2a6054d0ab015a03f708060fe8203c3fd0818145a1fcc40587f010121fa44060853000054b5dcaa6fc21e51210fdd843b16e21e9405980ed01d211ac2468002,
0x1030204d0394847b146605200a28144028605080a081390680132426084c2129a1fa026282e60698276824180ed01a603003fa080f038c20440e60814145a1fcc40587f01012000452101a5100a06b840401d3102e06fc40707e91018151c2a185410808214c0010b71059217ac0db854c0ab015a0000152d51329bf0ecd9fbb,
0x1101c15243ed808603a6205c3f4880c0a8e15a001283fb000054b5dcad89a21e0766e242043d21c4439098710ee4cf8a9d548d291e524c65787639960000a32a865c371c16e60c0814588e716da116c20089530132000052609a908a607e40f582b40f60076c419082608ec2068402080006681ff027784e4097c136815f0198,
0x10a98240c5b90b70059806fc40707e910180b240db85eb0a9a15602b400002a5aa26537e10f03b36aadc87110e48d402dd01810b6d152a254c15a09ba08ec03042a6054d16e00b302f5855804e8002c133844a00fe073040a029c08d41eac130827608a609802228079038c2044595828e08be000452101a5100a06b840401bf,
0x1106420983e9081a1008200019a03290ff813bc27204be0f0c136815f00cc0330060409a01290e5211ec23d0a33029005140a201430284050409c834009921304261094d0fd013142a487ab0fdc20183fa080f038c20440e60814145a1fcc40587f010122cac0008a42034a20142a381ae1010074c40b85410808214c0010b71,
0x10ab015a0000152d51329bf08781d9b556e43885bb0a0d01aa035000010f621e043c887137dd16ea1f1047581f303ce20b041008020ffc13ac270839006fa12b424f8118020e28305b9802e004e100400007d11474098c13f000b04ce0984130044a088a01fc03c829c051c293013b046a08be1d0822981f903d60aa03d801db,
0x106e228cc0a401450286050409c8340092e132426084c2129a21fc43b888a10e821c807a00bd0fd02dd0262834c09062dd42a405490f541eac2a687f4101e071840881cc102828b43f9880b0fe0202459588df000229080d28805035c20200e988170a8e1504202085300042dc45b802cc037e20383f4880c059217ac0db854c,
0x1101c1fa440602c90bd606dc2a605580ad00000a96a8994df843c0ecdaab716ee0df425004e106041ff8145882008b6079c4a98274001609803ed844504d2099c14e028e0132021803c844a04ec11a822f800611a0114c0fc81eb05681ec00ed8832104c11d840d080410000cd03fe04ef09c812f815f04db0330060409a047b,
0x116ee00085b8885316e00b3016485eb0a9815342ac0568035c20200df880e0fe8203c0e30811039820500e988170ff420600f0881d145a1fcc40587f010121fa440601b7000054b544ca6fc21e0766c5bc02e6139a276805c00b701662bf007480b216ec06b840401c61022073040a01d3102e078440e800216e22dc016601bf,
0x102d0059c0b3016502c804e426b84c1129a26983f4099409a626e407780ea05d20b901b40490092215602b407ee100c1fd040781d3102e1fe840c0a2d0fe6202c3f808090fd22030429800021e0766821e90f221c454b5dca9fbb556c2de42648a60069805a40b401390906135c260894d16ea1fa057e04d305ce0b901b40491,
0x10802085820100002a5a9bf148c82211d90a0e542ca89910e66dfc002930f16f8002c13f826704c2098012f825e08ae1128222809400fe01e447a85490f560002d5b283950b2a46541da85b507e0884dbe1b7e16f6276c046808600ec01d403907db088409d012d854700016ad948ca89b04429bf0769267e36fe2de83f58169,
0x102300acc256800c16ba0b1816282c409062d045af0b7505800aec15c00c606d011ec23d09b90a9a1538567054c0001734933fa8993b3443c8fddab355568a9d4878043d16fa2a5c09a8231046001340260a95083e107847581e7041c00944a803fc07f604f426087e8098805202b4054108081fd040787f3101606dc013802e,
0x10bc0177c2ef05dd0bb8030c5bf03340680243c3f6832f0a98156019c833e06820d081a2034500016ad933fa89b50b2a26541da85b507e766887946208d427eda2f08b7f058011e457e00c616ea0b1c23f047f00042df42a6054d0ab00002d5b267f5136a16544ca83b50b6a0fcecd10f23f76acd555a2a7521e02df85ad0476,
0x102e2000133faab53f7621d432bb9fa26204c08982130673f22e043f58a4e025205140a201430284050427304dc09a4133826504bb096c131009f81390fd01dfc2610a2d0fe620043fe87fa0ff01fd83fa07f00fdc202c415081e10302054409080f101220183f4880c0000a2649894621772a2e0023d82c00004234423885e1,
0x10e6c28c85280339068a1fb840307f010120000fdd06598c407ee2350887326022e0c577032606c80d2019e05620fda0c9426b87860ff41fb840c08060fd220883ff04e002f8059c09387361464294019c8344068a0000fdd06598c407ee2350930917042d580b98b570ac21dec530014510a604e409d077f0fe620341a0016f,
0x102481cd85190a5006720d101a287ee100c1fe840c00003f7419663101fb88d4221cc9818b8513a20d9019804d7097c0d2019e056202cc04c447e87eb156428c852803390f040d145c107f010121fe840c0b8300007ee832cc6203f704bf8985130c8d4221cc982130217081d0c198032606900cf02b104be0f0c23f80970123,
0x10fda15881b5855709b615603fe0b6410381fa45c30345068813240a387361464294019c80003f74aad432cc6203f704bf89852d5173f02e1c19e0a360fda0c943c3012517082e143f708060e6c28c8528033906880d140001fba0cb31880fdc12fe26144c323508873170c2bb81b2032606900cf02b107ed064a135c3c30164,
0x108bc114822988e7000223ac49602cb09062dd42a105470a9a15602ab8000b13499fd53a90f254aa9bf1531ab35674810f4ecea64321c843c087310e85234a47949310ec50bc43885c482b611ea11d815500c20fa41fa8481854c0a9a15600005ab654ea43c952a843d3b3a439087810e621d043b0871291936fc3b188750b88,
0x13b3a990c87210f021cc43a148d292621d8a178877285b51363b18a96285917180224564844b00016ad942da89b50b23b20765021f17160900483842f085c11482298000b56c43c9531ab35087a767487210f021cc43a148d292621d843b87630eca36fca0e01108b8a0480241c217842e11fe0ad823b00b8018002d85c400a3,
0x173f22e38134800b0894168004188f217140a3014400b00538028c147008f04f809d822d046908d4117822f845208a615243d58000b56c43c9531ab35087a767532190e421e04398874291a523ca498876285e21dca16c7630221171a2e2847c828c08b400045c589401282151c0001fb8727c21ced5b10f24df8a98d59a843d,
0x10a8e135c26684be0f0c155c2a10832104c20683fd07f60fe01fb819e0562100820003fe0829103020504090811101c202440307ed09de139026d07e91084210041f8198030205a00aa013402521ca44990a60028a05100a1814202822ac839b0a3214a00ec43f90339027204e82608782067c130800028993f74aad432cacd0,
0x1088610dc2258001171a254c17402dd05a827682460489017003a407100d901642e2418204a011ae2400190030905ea048008500fa01e82a5425a84a60930297825a04a5092e009410b002e004e00081fd8402080223ec00001fa03d807740e081f0039c07203a187d10e8427484ec889c0e922d942a6036406a40cc01930558,
0x1036e06e40002899556a21cd33fbb9417242e1c09c8a2d171c13043fa0b8f0fe020243f48b900000a264fdd2ab50cb27ee23102cd017222e1c09d01390ac82e3826084c20ab01fcc5b2080d0fe82e3c00028993f74aad432c8875172006e83d1081016c81fa440780003f74aad645e0b8f11a001f4035008b011402240440446,
0x1172c12f019787f00fda20282b209c00ab006dc0dc8b64101810481a3034506880d083f485620a8213145278b240fd02e503fa0b8f0e6c294000028993f74aad45ca81d112e02e480db81b91726068840b88050fd22e400001fba5132aad432c8b9417220cf83f9880b170029403f48b900000a264fdd2ab50cb2ee545c989a5,
0x116ea034c56e8b5a00042b843b08adb03d02b7c5688b9607fc15842ae8541164815342a5047d172a20840db880c0000a264fdd08754cfe195c5cb8a6002ae04d026704c4145a12ec3fc07f40fe02058408080a039206e84e007ec14a02ac80d9880c0fe620340ec081b03c820842b0856616480000fdd08752a5899fc32b952e,
0x1154411e440800020fe811ec26482c0069021605ab05570ddc1b8c1b6833c0ac41fac53007ed122222703c1018c02f805ec1bc817102de0dac09d0139067c0ce427504e009c2136826d84c1098428c83f40b9715641cd8528054a08fa2e540db880c0fe60ebc40687fc10381ff84110802105c000144c9fba10ea99fc5cc0ae0,
0x10ff4000826b847b0ddc1b8c374016606c80b0036e87eb0fda244442c089c0f0406300be017b06f205c40b7836b027404e419f033909d4138027084da09b613042610a320fd02c902ab854108242e6040107fe0ff80ebc3f981b7105c208840e080d10182ac839b0a500a9a152823e8b950000a264fdd087517322ba006301c1,
0x108fa2e5400028993f7499f85cd874305920aa015a04830fa411d85ba8903144403c007689da05cc0af851e8b410fce0b0015d82b808f6000849b0ace039007040d8054d1010203840889d215f027643f48b990a9411f45ca85410824000144c9fba4cfc54bc5cd0105117403b0075890d091a2ba05ba81d51442031840c8479,
0x151327ee8a970b9c16d602185b48a4915282a4c3ed82be04e828f45bd8b4105800aec15c0b2b113811ec000833e067200085210b80159c24d80e981ae03c207300e301bf034a06dc1de03a8078625c03a48b9a0a8e155c2a081d1082429402a688081012203840788111024205040b881d13a406884028af813b21fa45cc854a,
0x110340f5c15f0a3b147a0b0015c0a5408f615700010b7b16821d44595889c0f0404e4000833e067213045168a421700151c56707f303a606b80e601c6037e06940db856807780ea01d80a92134a1d2455907360a9a2014404080e101e204440a081713a41fc04048af813b2152823e8b9514641fa052787e9173229405cd8000,
0x116b4240c5ba80f801ee120c24c82c905e428e85ab0a50156427643fa080f038220380e408110a842b6c001075113a406c0404054d0a9405bc0b884da0ff820680ee87e8149e0000fdd043e10e6438933f952f21dd62688791d9b566e99f137f0b9d0fda1bc44210840107e1fac37606ee0dda1bbc3758b7816ac09f822981db,
0x1149e2be04ec854a173606c040401b703702b380e08b9c101c1fa45cc847d172a000144c9fbab13443c85cf87eb0de01bb037706ed0dde294055900003f75734897f130026184c388788b9e03d0208025007fe0604238854a8025005c009c1fd840100001f443a102d305680aa03f5848908ec1f4837806ec0ddc1bb437780e0,
0x117382be04e909d9101c20203f48b990a9a152823e8b950000a264fdd0ba10004288023d878205802b303c805e90bce178c2a5047d172a1fa45cc800051327ee88798ba012061f4845602a813a22bb8164848316ea2e780b98b9d02e205bc26d07fc1034077415f0a3b147a0b0015c0a5408f600085a0875115b615344e907e8,
0x116562dec0008a420a8e074c0d701cc038c06fc0d28568152426945d10817102820444070808100a15701ff0af806d026e420905410a9815945d080cc08f4000144c90f2b13610f555a08731746069c3bb0ba10000a264879267d087a43888773b352a5e2e8851e82c00570295023d855e00042e7c5a0875117402b380e081b0,
0x10abc15882b303fe067c0cfc15d82c008f62d04066047a15f00da04dc84120a8215302b28ba1036606dc40607f3101a076040d87fc1038079041087fe1044200841707e91746000144c90f2b13610f555a152e174a030c23b0b7d167815942af03fe06d026e4209054117420b0023d8000513243cac4d843d5568a9d559a8ba4,
0x1097606e809f813a02721fa03f807ec0efe130840501e403b01fcc4e00821103620343f48b92036e06e40d98b800680214c5d085610acc10482a080005133626d55a8ba703d01d8c5d288210fd22e8c5d083fe0a82000144c90f2b13610f555a0ba6131a1fa0164090e09042e9019a076f0fe81fc0408080a037427003f60853,
0x1037420283f609c010a615842b1056607fc10482a0833e067e00085d30ba70a9815945d081b3036e20303f9880d03b0206c3fe081c03c820843ff0822100420b8000289921e5626c43a952e17522be05ba836808fc134c487054c0a9a15940001fbb21e47ed955a1fb8087621d56a8acd321e0195c5d404c414c01fd009a0810,
0x1027e04e844a87ef09d4138026d04c10ed8214c2a60565174215841ff0541174e1fcc40687fc10381ff84110802105c215c0002899b13621d4a97865917542cec46b83680698135c264816614c024c80c6017c02f60df40b8816f027e04e427504e009c2136826087e81750030c23883340ff41fd03b78a2d103220403f801cf,
0x10a9815342b28ba10000a264879589b175a2cac5bd80011484151c0e981ae039807180df81a50ad02a484d28805101020384088814102e0000dbf267f10e654b85d60b3b11ae2d385a507e8175407a05d488210ac40cf819f8002174c2e9c2a605651742000144c90f2b13621d45d587d502cc2be04990750031805f00bd816f,
0x1035c06fc0d281b7134a2eb04298ba10a8e155c4028808101c205c0918124024a049c09401290288000144cd89a10e654b90eb39190cb2e7e497f267f175e02e03a8846b0360069c4028808000043d8879043b21c421cca978bae159c1d4439e81c10360069c0dc0bac1022203840408050fd22eac0010ba6174e10482ae0541,
0x102d207445d7814d0288135c26684c90fd004a40940127024a04900918355069812dc3c30368090a11f81d08329091a03785ba87511444283006180c2018011c44298bad102e068840287ee100c1fd040787f610241fe840c0bae0a9a15945d08000513243c821d90e210e6a9d45d80aee12d805200950001146629084a681d3,
0x151336268439952e43ac1965c9cb919176402185b587db15282da45498a4904e825b05bd81391656130400087f31484202c0e981ae03c207300e301bf034a06dc4b801d110a62e842a38557101020384088814102e20740d108050000a266c4d08732a5c875832c930026044c10983130a26184c2133f0bb1129a06dc3f58970,
0x1025c12f83f404bc07500cd05d80bae0fe81fc03f7080f10122018429854d0aca2e845d68000513243c821d90e210e62ecc0000b7c1352292409a814912d81fac5d78139098200043f98a42129a202c0e981ae037e06940db89a517582ec40938853174215082a185470aae2014404080e102e04b80978130026204cc09a0000,
0x109c0138426d04c109842ab4429854c0a9a15945d08557175a06cc1d781d810361ff040e01e410421ff84110802105c28b43f8080a138006dc40607f3101a1fa45d98000513243c821d90e22a5c99fc32c8bb4135a06dc4d28bb1028a13241a6047e13a002e405c00b7016a02cc23583290f0c04885d90134026604c4098012f,
0x106d0121424680de1444283006180c2018011c419a04bc0fd02ed03f8080a138015342b28ba1036e20303f48bb30000a264879043b21c454b933f8bb503b22d583f60aa2037420403fa04c90698226446b83291418030c3a8847101980cd023c84be058004c45300858126406300be017b06fa05c40b7813f02720d0019f04ea,
0x1101a076040d87fc1038079041087fe1044200841707e91766000144c90f208764388a970bb70fd82acc0d4881010141fd03f804c509780d3019a047e08e22dd451100f001da12341b404d30a9a15940d9880c03b0206c0f2082100007eec87900060876438843a952c2a5cb34c32b8bb6163c204c40c87f60ff4132c2698355,
0x1100420b80dc8bb710181fa45d98000513243c821d90e20cb22ee03f60ab30374202840807f00fe812f82648334069811c459d8a2201dc03b4246836809ae05980988a60126406300be017b02e205bc09f813a02720d0027504e009b413042610aad0fd02ed83fd081914422ed4429854d0aca2e842a10bad036606dc40607f3,
0x10000a266d5b043b6ebaaad843a952f177402e03a8846b16a022683f40bb8176e1fa45d9854d0aca2e84000289921e410ec8710bb90fe8204026481c106982ba007700e7091a12283ea87d302cc05685300932031805f00bd817102de04fc09d013909d4138026d04c1155a15944298ba1175a06dc3f9880d0ff820703ff0822,
0x10aae2eb4000289921e410ec5de8b1e1032204c3fd07f609a6132c3f40bbb177406dc40603681742000144cdab60876dd7555b45c210ea2ef0160085808f204fc1a0033e098213085d081b710181fcc1d7880d0000a266d5b043b6eba21d432c8bbb027e216026082c0067c1fa023c833f169c06e45d081b710181fcc1d7880d,
0x12a462efc4b801a212ce2014000589a772854b0a970873177c2bf016002bb08f20d005c001d3035c07300e301b7152426945d8817702b405500a9815202a0053c26f04d1099a1fa026587fd0ff00f0c3fb01c8103c205c40a88141024204440407e917780dd81af035509341234245048501f803a407100d9018c2ee44298ba1,
0x110201fc03fa04bb098804b853007eb02d205a00b3816602ca059026907fa03a420640001312000c21d432b92fe26144c40a95bb961780274409a81690ef605205198145026804c4098012f025c134826204bb0ff41fd03f80819102020280e781ba0352214c3f404c2027204e83bf87f3101a0d000001fbbb134aad443a9310,
0x112f615080001fbb21e5626821e9fb821c443b8ec51d963b3821d4a961fb60cae54b8a95a67f1784131053007f402a8204026501bd16ae1fd85ab081314422c785e001d9036a1fb05df813f027404e43f4077f098407900ec07f31042206c40687e9177c06e40db81b317000d004298ba10a84000144cd89a556a2f04559880a,
0x1b9a443c821e90e2566a76545e20a2201da11d84ed02b405cc15302a68000b9a443c821e90e24cfcaadd31e2a753b362f0c06a0a0c0186120c23b02c9056828f419484b70fdc201c487033403461fd025e097410201fc01138226044a089011181bd1014103c4d48b56138015342a185440e422d042b281b51018076440d8000,
0x1137412d425309da12760dc408c031d06200c1c172893d095a00305ae82c50588120c5af0b750a9815342a705470a9015243d507ab0aae0ae015d847b168203305e200c608f415940001fbb21e5626821eaab43f7076716a92d565abc4c4432b952b000699f955ba89b566aa46537e1d9a21e02f145ba84830bc00b182a68000,
0x1168203305e200c608f415940001fbb21e5626821eaab43f7076716a92d565abc4c4432b952b000699f955ba89b566aa46537e1d9a178c002c138827004a21f6c395866a010c200414e028e000c139c235045f011e09f013b038a03360610229045316f412a827704e302ea21fc43b888a10e821c8442010e07300e1400084d9,
0x1100820d042701b51018076440d800012f615080001fbb21e5626821eaab43f70767043a93110cae54ad33f2ab75136b5445e40b7501e0120c4ed02c905cc2f182a6054d0aca031823d00003f7643cac4d043d55687ee0ece2d525aacb57898886572a56000d33f2ab75136acd548ca6fc178e23442ef85de0bba2f1415d847b,
0x10ff420645108bc2000006d44bd854d0a9c150815c02bb08f62d0406600c608f41594406084e00007eec879589a087aaad0fdc1d9c10ea54b098886572a5c54ac5e48329147a2f0c25b83340fdc12f040387f0034620281f70ab30e4008040df0a23178e052848704c405700aec23d8b410198031823d05650ff820704000828,
0x13b2443c45e5800a0428082010382050408080c101040007e615103908000b13498f537e800317940c38255000c021c0ac0157075f137811d816400d616b4120824087710ee628f41c5032909ce12dc40087ee178620ac403833403da068c25e042407dc1fc011c0201035a20285118ab3154420403fa0bc802d60da026904d3,
0x10410164451d0a230a840002e6910f2b13410f487110ee3b38a9d542daab75136766d33e10f04dfaa46876410ec179a2d6823b0118056612b40060b5d0588120c5af0b7517960a902378a3d0a9a15385a08bc400017348879043d21c443b8ec51d963b38acd553aaab73b342f3046885de0bba0002e691d963b387630eca1d9a,
0x110180cf819f8557075e1fcc40682c005760ae006600c608f411ec5e08bad00042ef42a605651742000144c90f210ea548c8780bce000c19a843f887710e821c8442009304fc001400d0019008200f04dd045208a6004c00783f60820276800083ef00000b9845d87431794274415a047616b415302a685430a8e15203d50557,
0x105cc2cbc1be84ad13b4223844408d7023003b85e6894102ea13641b8849805e628e82c8822714460b242418b750a9a15082a185470f541ff040e07fe10442008417013709760528262015f099c1fe040b01c902d6134815f0bcc06d0134c3fd0819039e0cd025e07f0101406a448707f4102006e842707e8098204fc42c01b7,
0x105700aec3fe081c0ffc20884000828100820d042707e8098204fc42c01b710180cf819f8557058011ec5e08bad00042ef42a6056517420ebc3f9880d0000a26487908752a462f3c32f0a4c000a10b801f003d004a0070453093f0026003c20883fb07e809f8509094003200fbc000045302fe13a44e88aee156e000426f8390,
0x1005c009c234846a08bc117c4a0800107f80fec2010401033606100ba892c000013b827184d913a226a41cc038506e20b9815a04b4094a125c4ed04760242042c07d00f001862f3815f0bcc02d60da00a50334026e1348269890e098812f025d87fa0fe81fc040c88101014073c0dd01a90a84150c2a385490f560318066047a,
0x10fd82f240d9880c03b0206c0f2082100007eec879589a087aaad0fdc1d9c10ea54b098886572a4454b85e881dd09301fb017981d903b0000021ebc162a4c54b0a9215223b369bfc5e8000b0b5a0900453042f085c2930473828811d61168509017f09be0df4250030204ec2a54058029c0148028c1470453165608380128216,
0x1177a15302b28ba1100a202040708170fdc20183f808090fe8203c3fb08120ff020543fd08180ffa20783f48bd20000a264879152f17a62d2851d8b5011342d380ee8bd1179e1fa0260813f109c21601d787f3036e206c406880c0aae0cf819f80c6019811e8160047b17822eb40010bbd0a9815945d08000513243c843a8bd2,
0x110100000439952e2a582f5005b8bcd05921f4852481750bc40b201538b7b1656136452680010ff8290840d017a02d6057c0ab014a026e04b01b881dd09b8134826704ca098812ec25b04bf10b028ec51e87e8036e07540e081b01744069c51801b810ac151c2ab833e067e0ae015d82c008f62d0406600c608f42f045d68002,
0x111b80910204040307e200c80160014000a275800d801a003200601fb021b042a081c100000a041a0830105820a04120ff4012801f0a86151039085470aae09b8137827104a0094c125824e0001626941ca9195076a16d41fa84704426df0dbfc1eb4cfa001531e8cb832c0cc905ea81d1134a1fb040b81a00342068840281a9,
0x10e420002c4d196032bcff345eb88d001060254225045704d60a0803e807c00f601e8206094a088a00d41f78263000a22c0204020b0414082410301fe0b12088410d820e040e08002ab80200042008801180240fc2150c000589a5076a16d41f822136fe001531e8cb832c0cc94caf8bd600f222d002e005b00b411143e70263,
0x13b3821cca96930a4cfe99f432c931025fc4c380028cb832c032b86580cb219686558cac195517b22dfc26284bc0aae1fc040487f4101e071840881cc1028078440e81ae1010074c5ea0bd3102e1fa45e9033c067e0af823d8bc1175a00085de854c0aca2e84000289921e499fd33e865717b00028106820c041608281048544,
0x1014e206804b0095012811880ed8457052c114c141042504fc252402984160816101c4ba82350450087410b88530a881c842a407aa05762d0406600c608f415943fa080f03dc20a45bd8b2b000229080d288050a8e074c40b81bf101c073040a01c61022078440e81ae1010155c1b409b9057c11ec0001fbb21e5626821eaab4,
0x117b2151039080003f7643cac4d043d55687670439952d261499fd33e865926204bf89870005197065806570cb0196432d0caf195a32ac6570cac0bdb007600142088587044a150c01000210044008c0120000b13499fc0028cb8664a656c5ed05d2138a2d001a600fa05e2132424b849814c005c41b884da09b621dc3fe0728,
0x1037e20380e60814038c20440f0881d035c20202ab80003f7643cac4d043d55687670439952d261499fd33e865926204bf898700054c7a32e0cb00bde007610444a58226004000840110000b13499fd33e80051970cc94cae8bdd0076001420885860448150c01000210044008c0120000b13499fc0028cb8664a65645ee000a,
0x1b13432e45f000050076009000e801b0034006400c041107fa0fd8113820f04102f782a180003f7643cac4d043d55687670439952d261499fd33e865926204bf898700054c7a32e05ef803b000a10442c2822317b62f745ee0bda17ac00900118022004200805ea854303dc20a413a8b7b1656000452101a5100a151c0e98817,
0x132be32b45f180050046008801080200a862f8000b801c000162699720cb6664a2f882c28bdb000a2f705ed00230044008401003fd17ae150c00b801c07e808181fa8bdf17c00000fdd90f2b13410f555a1d9c10e654b4985267f4cfa196498812fe261c0014cb0195e17c200282c885900b1e16382c6858c0b1615103908000,
0x104360002d5b283950760884dbf80051d903b287660ece1da8657c6588be511a001d8225044204d6096c2060403007000ac10a822100016ad948ca85b04426dfc0028ec81d943b307670ed232be32cc5f200941168115c3e70282048810701f880470020151c100022e00016ad941ca83f04426dfc0028ec81d943b307670ed4,
0x1b13410f555a1d9c10e654b4985267f4cfa196498812fe261c00145f38079116811143e70263048810201f88030002200145f28be417c6162410d82000a86151c2ab8be00001626941ca9195076a16d41f822136fe00146550cb41d903b287660ece1da43b50caf8be600f222d022287ce04c6091020403f1006200482a38200,
0x117a82f4c3f808090fd22f485f00bad0000a264879267f4cfa2fa045a07ce00f2091022283f104c600542040be20fc20ff410e020f04022f845f3006800ce0194032006300c4007000b843607e809345ef854316f62cac0008a42034a20142a381d3102e06fc40701cc1028071840881e1103a06b8404055717c00000fdd90f2,
0x1138a03e807a02f305e2125c24c037109b61ff040d01db08a609f82b280003f7643c821e90ee3b147658ece1d8c10e654b41109b7f4cfe196537f8be90b1200145eb8020008000fc01f003d0076089c1fc83f8081c103c0000be7027a04e44a684c10fd02f602a10543058011ec5e08002177a15302b28ba1145a1fcc40581b7,
0x10ff805341a60334065204a409381250246206826504c5098812f025b84b603b61fa02298be904fc214c15c02bb168215943f708060fe020243fa080f0fec20481b409b900007eec879043d880843888771d9c10e654b4110930a36fe99fc98726ff17d6089848484110af400fc000589a4cfe0014cb0195e19662fa84dc05d2,
0x1101c073040a01c61022078440e81ae17a82f4c40407e917a4155c5f00bad0000a264879267f17dc0028110021a043210302040573006c00c02a207210001626930fa63f000a6580caf1954195e2fb400502200434103020405770aec00dc01885440e420002c4d261f4c7e0014cb0195e32a832c45f604d906e205d451d8a33,
0x10afe00145f68bec008808a020a841617d62fa81070025042c009c1fe03fb16f81008200800015fc1f28141026b04c6115c2250445012801fc03c8b6b14922a505498b6917d015082a185440e420318066047a058011ec5e08002177a15302b28ba1145a1fcc40581b70fe020245bd8b2b000229080d288050a8e074c40b81bf,
0x104426df0dbfa67e1d8c3b287660ece1da076688728bf111a217802ef85de0bba0002e691d963b387630ecd10f117e02dac52480860110022404507db04e82fb85bd8b2b000229080d28805037e20380e60814038c20440f0881d035c20200e98bd417a6205c3f48bd20a8e155c5d68000513243c933e0bef001416082c08580,
0x10114022404400860fb609d05f70b7b1656000452101d3035c07840e601c6037e06940db8bd417a6207440b88141022203840408050fd22f485a082c005760ae006600c608f611e85e08002177a151c2ab8bad0a9815382b28ba10000a2648790bf2001821b4436086f10dc21c046f08840000767ad5b1d8a3b2c7670ec6152d,
0x103a607300e307f4037e1fc00d701a51016207440b88141022203c4070809101020143f4880c036e214c2a10be00a8e155c0670479000411ec2a60bc10aba0b003c805e70bd2178c2b28ba117e4000144c952d17e8069c5ea08050000a950a96087317e60b9400609da0ba617482e885d001dc26f45f88b7917e00af85f7808b,
0x1093c079c182010812a62a540fc81eb03b603104190826103411c440208000ff80cd027784e409b412f80cc018102e204d053001390992253426087e8098a0d3010b020e004a007c23f0b7c08040ff01fd80d700002bf83e5028204e809ac22b87db08940250043007f16d62a505498b6914922dec5958001145a29083f981e1,
0x10ff820703f48bf5066811c4062000208f60b003c805e70bd2178c5e0855d17e415302b283761742000144ca63c54a8a968a978bf613a2031049b08fb08e207540e401c103602fcc5ea081710222038404054d019c11e4001047b0a982f042ae82c00f20179c2f485e30aca2e845f90bf40000a2644398bf509c21ff81be8820,
0x1002e11c420883fb07de02e81fa00c400002bb84e88ab710a6150c5f00bf40fe620343fe081c100420b83f48bf5044e08bc51180ce08f2000823d854c17820b003c805e70bd2178c2b28ba10a8415745f9000051329bf533f8bf7145405e00bb813f027205ec3f804de09821ff43cc080a0fd0207c0d8089a03c4214c3f9880d,
0x1027213a826d04c10fd005ec25e0798066811c40620853000411ec16007900bce17a42f18bc10aba2fc82a6056517421fcc40687fc1038200841707f010141fa45fa80005132ed5131e0bf8145406300b7813f027213a826d04c10fd012f00bd87f00f3020284e00bf60934040c20e0047000a0cd001f003d004a004c235801c,
0x1105c1fa45fa82081446033823c854206d012340788bf7000411ec16007900bce17a42f18bc10aba2fc82a605651742000144ca6fd76a82fe84990131031805bc09f84be09d4136826087e802fc05f00bd84bc0f30214c5d087fc103820084170a2d0fe020283f9880d0fd22fd4000289976a8990e2f00bf9145406300b7813f,
0x117ee000823d82c00f20179c2f485e3178215745f9054c0aca2e840d48bfa0000a26537ea63d17f624c80b3018c02f805ec0b7813f09ae13a827004da09822ab43f404d30ff4206451081b106682fe420f004d115c006402083f608200fbc000074317942fe051687f01014214c2a18be017e81fcc40687fc10381ff84110802,
0x10bce17a42f18bc10aba2fc82a6056517422fd00d9880c03b0206c0f208210fd22fd400028994dfa2ff04990166031805f00bd816f027e04e83ea84ea09c013682608aad0fd022683f6046b03b202e8390074310a62fd00d9880c0fe620340ec081b0ff820700f208210ffc2088401082e0fd22fd451180ce08f2150824680f1,
0x1000411ec1600bc10f2017a42f385e30aba2fc82a605651742000144c8bfe14c005c409f813a0272132426d04c1155a1fa0262885317e81fcc40687fc10381fa45fa834c08fc035c5fe000208f60b003c805e70bd2178c5e0855d17e415302b28ba10000a2656a88bfd03601fb023881ac01882fec0d48bfa000411ec1600790,
0x1000098f153aaab721c410ec604854e18060000ecf8c080a9a300c00010f7180e15306018000087e30183d58c0000006dbc60287aa1800000076b8c040ab030000005cd3180615246000000370230082a40c0000003b64600854517fe0002d5b8c0008782ff8000022317fe070455108100fe82ff423f00d717f81fa45fa8bf4,
0x1102c06b440501d913202acc0da87ec154407040dd034d102013203fa016f09b404e4260837109b60d0026101b31018076040d81e410420df4270817b09c01ff8411039009d606302750802105c05680b3054217fc30006018c07180c0000a9606595aa4b3409891fbb262021d4983d89a5aa0302851100c4018012342388c07,
0x1132023345ab01be036a20300ec881b000025ec2a1030409400df427087fe10440c60257039009d620084170bfe1800301c60180000cb27eec43ab93ab13410f4a95aab73b3aa46937e8c0b05ba2b20246031806080bd449d0a9d095c128024c0002181229a857c036809ae1fe81af081909a20cd051087f814541fc05ab01cb,
0x12a56303855a093a156c0b2c2418c0c18160c8018c030405ea2d5424c04a006fa13843ff0822095c0e402758802105c12d41cc04f0100820d0063047a01f4125c5ff0c001806000032c9fbb566caad043ab93ab134acd421e952b556e30345ba80d7180e000087110f04df8df74606035e0918134416e87f81590205854e893a,
0x1100420b86038c0017fe2ff860180002a581964fdd8875260f626959aa63c087add71bef152a3b3aa46933f0c1010321fe851084d713721f541b400002a581964fdd887572f410f555b0c0f10321fe851084d713720da060681b1066812f83f8080a035804c40ad0166000054b032c9fbb566caad043a9307b134acd531e043d,
0x14cfe9bf48798c110fd806a43e9880a09181fc054e84be119a0cd000004760f820ad84fb811b0218042007d80ce018810c86060b751602120c22582cb05ba000455a0ac8153824e80d9880c03b0206c0f20821026205682a1049f094a0e142728800105012b406300fa181e059818204a006fa13843ff0822063012b81c804eb,
0x102cc0000a9606593f76acd955a0875260f626959aa63c087a30501658483156c30305ff0000b134acd421e90e221e0767548d285e50cca49933fa6fc182611d815b0b5a16202b3846b88d6018c11e807a00fa092e2d546038c060000acd955a2a7a5504ad0ac4d2b35087aaadd53a90f218242d5807d80ce00016269bae37de,
0x1036620300ec081b03c82084000152c0cb27eec43ab97a2a54aad860b09c0036020283f804be06680000a9606593f7621d5c9c267f54e830544e001b010141fc025f0334182430446098c1006400c6018202f516aa303c60700fa018c12d425704a0092e126023d037d09c21ff8411039009d62008417039809e0201041a0131,
0x1260f626959aa63c183203c42468b3b1806000155a2b3521d810ed33f2ab718301f280000aa912f6205860b07f80fa62cec268835e0914038850600c4018611c460a813102b405982a10ace11ae0df427087fe1044300c6038c06000054b032c9fbb556821d4983d89a566a98f021da67f182e20640e787fa0fd8135c3ea8368,
0x109d6200841708d706fa13843ff082215f0301c5ff0c001806301800006593f76acd955a0875000cacd531eaab74cfc306c510881913801fe80d684d7182c1f541b400002a581964fdd887572f498f555b0c1a10321fe851084d70faa0da060c0c17000430500b308d706fa13843ff0822180c0000a9606593f76acd955a0875,
0x118002ffc5ff0c050000a16548c822136f83b187671b7636fc3b2060e8c1318220c8018c030401f40bd46090b55096a12b82500497093011e857c0c060000acd955a2a7a5504ad0ac4d2b35556e99fd53a843d18381c8051180fb019c30305ba848305962ad018c030401f40bd449d04ae0940125c24c047a00042d2c60c0390,
0x11836306860c88d706981324605054206e2136c1a004c206fa13841c804eb073013c0402083414c005c409c813102cc24c809d04c102de13680be017b09c01ff8411018c09d420084170bfe18002ffc6018c06000054b032cad5259a04c48fdd931010ea4c3ac4d0c1e165828483dd07b714f610e4594877d165a1df8128843a,
0x10000acd955a2a7a5674aa0956126fd4cfe9bfd55baa75087adc71bee2a553b3aa4646100a2201da11c42468c07000043c955baa7521c410ec60f8b09089010d8033008000c43074594825304a2090002e8059165610e8217842e00022bc059a02cb13a20ad817407900bc6035c16382c508e4123859d847e08fe000860e0c15,
0x1031813a8401082e072c13b440188311806301c60300002a5819656a92cd026247eec9880875261c30883f601c1037420403fa04c9069806cc40601d81036079041080002a581964fdd887573f054a959a0c2115702b8c0008ab913e428482410a1705982be0066047a057e0bd424c030409400c602570bfe1800300c5ff8c06,
0x109061d684ca030518420c4823700b6141a1f745ad0116020e041807d00f4019812b825684a30940127c24b847a0004307c57c0c15182c105c20904040acc15782ae8541183c0598098893214c005bc0b884da027204e8260837109b60d00261037d09c205ec0be04e00ffc20881bf84e20ffe20941c284e5100020a01c804eb,
0x105d0276845d031806080bd407d80fa01e803386090c1c16aa12b82500497093011e856708d711a623582a10bfe180030186038000566caad153d2a82566aaadd53aaa7721c4ad0ac4d043d184a20102780832073007e800006593f7621cca97ab4318482ab42b08c22000019656a92cd026247eeca96131010ea308c1658c20,
0x10e7a07380d801d50382225844b81b817e62f50414881d102e2050408880e101020145ff8bfe180030186018c07000054b032c9fbb566caad04398c2701da287860c048d03821cf40dc0c07180c000155a3b3576aaf055d9bbb577676ed0ca97aab721d810ec6130416000008a84668a2301d0035c246048305ba0b2c5640ab4,
0x1020c041c24f837d09c21ff84110116095a0e402758802105c300c60380000cb27eed59b2ab410ea10f559aaab754eb626c614000115702b2450902dd05d00b2c246093f128025044ed048301ca2b8c4dd0a0d0fcc2d6820b855d0a820c6018202f501f403d06128a30095c128024b849808f600086130c2411ac234c46b8ace,
0x12a581964fddab3655684c4421eab35556f626c615055e138a2d5449e87e7019811e815d847b01e803e824b8107093e300c0001fbb566caad153d2a82087aacd555b9d9c18523080165846e090602d84de8a0d0fba2d6820b8412080815782ae8541070a13944000828072c13b44018831018c033023d02bb08f603d007d0497,
0x1180e2ffc5ff0c03000054b032c9fbb566caad0988a91a087aacd555b8c2c026e0adc60a847518380e602780804106830a41c804eb100420b81be84e10ffc20883f48c2718540000a9606593f76acd955a1311087aacd555ba67f185604dc15b8c1508ea1048614054118520e402758802105c0df427087fe10441fa46138000,
0x11810301c6018bfe18000000a9606593f76acd955a1311523410f559a8c2d0fd806c00d4880a0fe011d84c102b6086403105808b75181a112c241815f00020b2c5640a9c156824e860d8c2b0a8430a861481b31018076040d81e410420df4270817f09c01ff8411039009d606402750802105c1fa461380c608f403e824b8c00,
0x1119a000016487d009060394184030206340c5817982be141a1f740af898d0fce150456402e9082405ac4dc8491181e0da0616017f09c0064027504a0095c12981c284e5100020a0259039609da200c41880c6019811e815d847b05d60bc424c00fa092e0418083849f06fa13843ff0822022c12b41c804eb100420b83f48c27,
0x1057611ec3f48c2717fc300c000152c0cb27eed59b2ab42622a46821e9d9c185e20400de87f418421324165014a131a1f9c55a02e902d626e42488c0f06d005fc27007fe104406402750802105c0d302410c0317fc3000000152c0cb27eec43a9311523410f4ecb1d8c3b30acd155b0c2e102c1fe055484d10fa60d782460926,
0x10576126023d817f09c01ff8411019009d4200841707e9184e2ff86000c03000054b032c9fbb566caad0988a91a087a30c040801bd0fe83084264814a156c0b282af09c5127a1f9c0bf84e0072013ac0c804ea100420b80cd84ef100820d0066047a01e803e824b8107093e0df427087fe10440d302410c2e185a0bc41758498,
0x13f7621d559a267f73f030c840b07f813201344408035e0fe8122c61084c905ba057c0a50ac8156805fc27007fe104406402750802105c0d305ff0c00000054b032c9fbb10ea4c4548d043b5668767544da67e18622b200af893a18162adc0de80000a8420404bd85660fe83084264814a059830bc6170482069830b417882eb,
0x10126023c03480d808c811642290439125a00042400b2f1424285c166014a186430c4174031f062e0c0c17a02bf02fe13803ff0822032013a8401082e033613bc4020834091c30005ff0bff000054b032c9fbb10ea4c4548d043b5668aadc8711d9d186606f45ab081003b206d42b307f418421324406081b06980000a960659,
0x109c01ff8411019009d420084170bfe180a30085ff80002a581964fdd88752622a46959a2a744cfe30d45208b56085c1504453041701262ae0229092d142e28484a0894002fe13803ff0822127e06402750802105c2ff86000bff0000196443a9311523499fd48ca859044230d02ae0ad411ea04dc2170c15114c307c056009b,
0x110ea4c4548d1d9c4cfca9d8872a91918700004226843d010e01c85ff80005232a2687648c37132006f83f601c9102c1fe026887d3036620300ec081b03c820841af00002a581964fdd887554ec9bf5c9d0c361574096c2ae000b0498096412c025704ac095412a0433087c000461a093f12802504509013702943054619017f,
0x1183e2dd43f38c3301e003b807680ec01d612382468af806982ffc5ff0c00180e300c60300002a581964fddaab410ea4c4548d043b5668aadc61c8aa91236205821f07f8000230d826887d30872057c53d8b66186e2ad00bf84e00ffc20880c804ea100420b81af088410e421d0445087710fe2ffc5ff0c00000054b032c9fbb,
0x1017a030806182ad05600ac81598c03180e2ff86000bff0000196443a93115234a16d33fa9196e3b0f141108c3b1590277c5ff0c000000a46942f2866556d188942da67e1874250409b8942097c057c3f80c36101406f455988100fe83084264814a187021fc43b888a10e821c844207ea0916176816d09f805cc104861a8334,
0x1088c10f459780011876284850b847208e2052861a8c32187405fc27007fe104406402750802105c0da06000bff17fc0000a9606593f7621d4988a91a0876acd155b285b18780ad04dc024e132828303d38a480fce250821a82b60158026c049808f00d230d0232045908a410e40c804ea100420b850b8a1202fe13803ff0822,
0x11424285c2390471029430d4619017f09c01ff8411019009d42008417019b09de201041a015f187830006028c021806301c5ff0bff000054b032c9fbb10ea4c4548d043b5668aad933f8c3e00002adc55b03f712f6159860d0c1617fc0000a9606593f7621d548d285e50cca49955b267f5232e5e861e88d000ea01d00398c37,
0x1104406402750802105c30206018c05180430005ff8bfe000054b032c9fbb556821d4988a91a0876acd061f808f14f6026c2d0000b0158093815a09b814180b5852407e7091610d415b029705100a14049827c04ec09440348c3618681194232045a08b21148229843a087224b40008b2f02d630f415982b205600ab406180c2,
0x10cb27eed55a08752622a46821da67e188012181aa8999168224a016e02db05b40b6416c02d601cc1110245848a04c230d800588cd037a07045240b2d000020400450089010c09d0139827104e009bc137097b0fe8112c2260c21099200040a507e715382ad0618854113be104861f015f18780da061c834c109e05fc27007fe,
0x1000054b032c9fbb10ea4c4421d90ee21d899fcece289b043e310461b02c90914234407387ea1490021822587e700020b2c0af8a9c156830e84ef8368183005fc270019009d42b3846b88d306fa13843ff082211ac0e402758802105c0b0816182c4058a0b18163847f01a0034c23f0c3f1806301c6000bff17fc3018000152c,
0x1001623442d007ea14f6292014b80ac05100a1404f009b0126023c13e027604a201a4220846508c8116822c845208a610e821c82c205860b1016282c6058e1f9c1658c051804300c6000c0717fc000148d285e50cc43b887610e621d1121487210ea523008846210c1508e204dc5ad043214902c04043044b0fce301c6000c03,
0x1044a089011182c9081c103c5ab000017c01c842a203f7134007640da897b0acc306860b07d502d631040008c420fce0b2c406081b02fe13803ff0822032013a8401082e05840b0c16202c5058c0b1c06800d3180630006038bff000054b032c9fbb10ea4c4548d043b21dc43b087310e8890adf7533faab65230310c12e02c9,
0x108ca119022d045908a4114c21d0439125a0004597816b187a284850b8c4302fe13803ff0822032013a8401082e033613bc4020834180a30086000bfe17fe0000a9606593f7621d4988a91a087643b887610e621d11215beea67f556c311046a0589110621f843b087310e221ac0050b7512ea2fc0020003f007c00ec1138226,
0x1167612386220c40058e0b1423f047f11ac234c46b8ace187e0008618019b03200e400bf837d09de13a827584e009c205d440208020ffc308c41a082e10441fa4613834006e2136c26d04c217fc300c60300002a5819656a92cd026247eec6228b5604fc094c2ae000b0b4029ec14b80ac05100a1404d8093011e09f013b0251,
0x10672130809c813a0982285c1bc84e102f605f027007fe104406302750802105c30005ff0bff180e300c00006595aa4b340fd51fba523410ed48cb7dd10ea43c955b2643188e05f84fb00d71598300c00039fa72f07ee9beea67f727ce7f9ca3398621e631182390c15056c04dc56a02cb063e0c5c18182f4057e1e402ae82de,
0x111b829bc53d829701580a20142809b0126023c13e027604a21194232045a08b21148229843a08720da81b58339142e28486000bfe17fe000032cc6a28c407ea8fdd291a0876a46542f28664cfe7ec00031fae3b3a08846240a6f1490024c0348452087200045978b7506cc27bc5cf091002fc0de81b5036b09b605bc0b884da,
0x1031810806238c4609d8200c41884ea100420b82720800105013803ff0822098213685190c0017fc2ffc6018c07000019656a92cd026247ee948d043b5232df7542f28664cfe21d555b130e18941fb4518836612582cbc1b5036b0672285c6000bfe17fe000235146203f547ee948ca67f3f600018fd74623043e312451887ed,
0x110001ff841a0831105c20a041104da098228c806a047e17fc300c00006595aa4b3409891fba523410ed48cab355568a179433267f10ea312c5240069189010e40008c4909ae1fe840c81d50e920f0c3fb848509981e685ba816602a22e78499091109b605bc0b884c2027204e855900d001a4034c06a00d506f213840bd817c,
0x1137403c407800e913c22ad060c0c4b01a0035006a847e180e300c5ff0c00000019656a92cd026247ee948d043b5232acd555a087550bca1986268c2617a82764414881d102820444070808100a300c000152c3f7410ec8762ab410e6313055b039713ec1e0862505410840311c59d8c4609e013b027504e409c020104018802,
0x102b405441c9838d07040db419e0562188e2cec5cf0932117022703c1036a06d6136c0b7817109b40ce42610139027413045190ab201a0034806980d401aa11f82728800105013ac276880310620de4270817b02f813803ff0822031813a8401082e1806301c00006595aa4b3409891fba523410ed48cab35556821d4fdc0c4e,
0x108fc1fc86228c0718062ff8000152c0cb2b5496681312523410ed48cab3518a031341c7037b189c13ac27088020ffc20b841107e91898311406a047e000054b032cad5259a04c4948d043b5232acd555a0c4f0f940d6c1b204d109ae1fe03fd0816103207380ea8749078612283fb8000090a038826607d008401e685ba8166,
0x172f04c48fdd291a0876a4662f345ee8d5c4c08984130421da315055b0b5617fc000148d2919b13499f137f285e50cca49933f8c5303822f5040700002a58acd04398c52038220383a487e907622d90601800090787ee959a2ab518a212143cd01c80fce20443a482bf019a1fa41d8847808ee2d9062780d501a8034c06900d0,
0x11564285c62887f218a80630275017c02f613802780804106813ac401082e098228481bd84e10ffc20886000c07180630185ff0bff00001965cfd2cd026247ee948d043b5232acd043a952f50cc7ee533f0c5513c22ad06298397071c0dec0b9813d0f0415843f5848d0dc603b80b78171027204e85590c0317fc300000039fa,
0x1127e30146010c0017fc2ffc00006598d451880fd51fba523410ed48cab3410ea54bd4331fb94cfe4c1d42cd89a18ae314c0b9813d0ac20001cfd39785234a465433285e524c99fc9878c56150a21dc445087410e426e82ed07eb13f028405ba82e805cc03c407800ed091c123457c09df06cc30dc55a016f02e2130809c813a,
0x109e0201041a04eb100420b827087fe1044130426d0bff18002ff86038c03000019656a92cd026247ee948d043b5232acd043a952f50cc7ee462c000b11501680508029705100a1413b025116562a60624046508b4114c21d0a07000206f859a0ab60a840de40e0839709e0201041a0344069628484a0894006f613843ff0822,
0x118b424c85050782156405ec0be04e00ffc20880c604ea100420b860000000cb24c0098513123f7410ed48cab3410ea54bcfdc0c5900022cbc55c0a07082e15982a08c57066412f83f8080a036011c45ad0a0b0dd0056809889321598315862a8a12072e0dec1a584db02de130809d0a321564285c62a018c09d405f00bd84e0,
0x11544131c26408100fea0ef03a48c5a031805f00bd837909d4138027088020ffc20b841107e918a431401b5036b09b605bc0b884da0672130809c813a098228c86228c03000054b032cad5259a04c4948d043b5232316c62c038e18b205bc26d013a098213ac401082e000019656a92cd026247ee948d043b5232acd043a952f,
0x106d6136c0b7889c06721308530078202e2136809c8ab2027413046000c030000a460fdc06592624b549668043b3f7421d462f01be0690282426487f41020070460180005230196421db9f810ea4c1cfdb952f5668317406c8b16090a11ac1e183a10e92300c000043b3f7443c843ad89a8fbb1f7ca970c5c117005241a4834b,
0x11806000021d9fbb10ea196487710ec3b38087e311130718c013243fa0b86101e1fa462f0a600f042ac80b884da098404e409d04c10000a460fdc06592624b549668043b3f74317c42c02cb037e11fc0e10c5d10ac31703fb87ef099812e42b10151024c22e03f5818c02f805ec1bc84ea09c0138440107fe105c2088519036a,
0x1105c301c6000bff18063018000291808767eec43a8659261cacd463187fa09ae20640b581d3000021d432c952d8c444c4544d0c620fe012f84050137035c000043a86592a5a4c462f0285818c212f83f80334101411c40d70b5a0864292058080860896074c40c87fa09ae05980988c4510a61ff040e07f3101a1f9c6038c00,
0x10fe62034000291808767eec43a8659261c319019a047118c22d682190a48160202182258c620fd631801b40001167631083f380d301a00b2c46b08d311ae2b3823f047f0680130809c813a0982076c40d81e7104207cc62288530fe62034416816f02e213683fe081c06fa13840bd817c09c01ff8411039009d606302750802,
0x172f4e4e130e3918043e31981948a250f0c0d783f704d1100e1fe00d2881611f40730044008604e82b20225844c03b6206c0f3882103e6311442987fc10381fcc406882d181030005ff00003f7621d432c843b727499f930e3918043ea26c6328a60029413241a60c63027204e8260817109b41fd040801bf188a214c3fe081c,
0x1105c05f827007fe104415082b087f4102006fc62288530ff820703f9880d17fc30005ff80003f7621d432c930f0876a46159a0c6713a806940d7080710141fb83f80786097c0ca419a046b183e240c07880ed15f012344ef07dc18ca311442987fc10380d0026107f3101a30006038c0600007eec43a86590876e4e933f263c,
0x10ffc20882a1056102560000fdd88750cb24c3c21d821f5134e46137e8c6812fe0970056009b011e01a4220846408b2114854e04390002319809503ee026a08040b48bca14462d580ae8a7a11800d300ed881b03ce20840f9882d03f220cc55000000fa0064c27608031062060c2720800105004f4260817309b4063c2750802,
0x110381fcc4068c03180030180001fbb10ea1964987843b51349bf063501c01272319c1a60c4510a61ff040e07f3101a0000fdd88750cb24c3c21da89a4df8acd06348c6602ba04d449508cd17942d580a4885300001f400c984ec100620c40c184e4100020a009e84c10fe620340b984da0ff820700c784ea100420b80bf04e0,
0x1044e0898112822404460b2c207040f18ac277859d80d705920b1c16302c505880b0c16108d708fc11fc63483400984076c40d81e7104207cc41681f910660df427085440e422f8000007d0032613b04018831030613904000828027a13040b984da031e13a8401082e02fc13803ff08220a8415843fd081903a6311442987fc,
0x13f7621d432c930f0876087d30e8c6c07dc04a81008c68144631a800007d0032613b04018831030613904000828027a13043f9880d02e613683fe081c031e13a8401082e02fc13803ff08220a8415840001fbb10ea1964987843b043ea26863588d40b1221cc438886b10ec220c43f000a15d025d45f80040007e00f801e803b,
0x1156804d420783f3044a08144ba0a23040207fc0fe81fc07dc0d0026101db1036079c41081f3105a0df427085440e4200003e8019309d8200c418818309c82000414013d098205cc26d018f09d42008417017e09c01ff841105420ac202183f8080a035c10c8580844b18d6311442987fc10381fcc4068c00180e30185ff0000,
0x101ae034c06802c9058e0b0846608d611a6235c23f047f02ba319c6328ab403b6206c0f3882103e6311442987fc10381fcc406882d06fa13843ff0822072013ac401082e010c112c635812a18d830006018c0617fc0000fdd88750cb24c3c21d821f4df899f86368a481418030c06b82cb08e2235c567047e08fe0cd063384be,
0x102fc13803ff08220a8415840001fbb10ea1964987843b043e31bc5740a4817e0035c16582c9058e0b0846b847e08fe319c62b0c6d098213681a004c203b6206c0f3882103e620b40fc8c4510a61ff040e07f3101a20cc1be84e10ffc2088043044b18d6300c6000c0600007eec43a8659261e10ec10fa6fc18dc23745240bf0,
0x108c8027804d8459012611480ed881b050a11680f38821052e11940f98c4510a61ff040e07f3101a20b40008c6f180c2ff86000bff180230100001fbb10ea1964987843b4cfc31c00ae8c65119a2d58637012a18d831ac00007d0032613b04018831030613904000828027a13043f9880d02e613683fe081c031e13a8401082e,
0x109d620084170c0617fe0000fdd88750cb24c3c21d8c710fe012f84050334035c307c078843615f01234126813513bc2f283ee0c6a153805a41a004c200001f400c984ec100620c40c184e4100020a009e84c102e613680c784ea100420b80bf04e00ffc20882a10561115601d42d0027608a60194003008f00de01a421c80ac,
0x109d62008417017e09c01ff84110aa00ac2031823d034009841fcc40680fa092e0008638837109b61ff040e0c0600007eec43a8659261e99fc6390c4201a6034046b08d311ae2b3823f047f18ce3158638000118de130426d03400984076c40d81e7104207cc41681f9188a214c3fe081c0fe62034419837d09c21ff84110390,
0x10ff820700830107093e0bf818004a006fa13843ff0822022c12b418904ae000431c41c804eb100420b86390c08180e300c60300003f7621d432c930f5230acd62428c7316aa26241a603681818052053d09b913ec315826084da09c8200041404ea09d8200c41881db1036079c41081f3105a07e4622885310660df42708390,
0x1000010f533f375e3b3aaad863a04d106bc1fe0246081602ba24980e608cd187403941648368114200305a587e705960b140ed881b03ce20840f98c4510a620b400007d0032613b04018831030613904000828027a13040b984da031e13a80bf04e00a841584063047a05700aec23d834009841fcc40682eb05e212601b884db,
0x118e81e402f38a9d02ba2dd4462048318e6076c40d81e7104207cc6228853105a0ae015d847b117431c807a00cc018c11e81a004c20fe6203408b04ad072013ac401082e020c041c24f837d09c21ff841100fa092e0008638837109b61ff040e0bfe1800300c6038c0600007eec43a8659261ea46159a8c7505d212444f08c03,
0x1037e076c40d81e7104207cc6228853105a2a802b082bb08f60bac1788498117431c807a00cc018c11e81a004c20fe6203408b04ad072013ac401082e020c041c24f837d09c21ff841100fa092e0008638837109b61ff040e0bfe1800300c6038c0600007eec43a8659261ea46063b04d106bc1fe0246081605ba0730564093a,
0x101f403d006600c6095a127c24b847a000431c41a004c203b6206c0f3882103e6311442987f3101a20b41b884db0ff820701be84e10ffc20881c804eb100420b86018bfe1800301c60300003f7621d432c930f18ee13441af07f80918205816e81cc159024e863a098d0594036054e815d14f423002408482069831d43fa0810,
0x1188a214c3f9880d105a0dc426d816f02e213683fe081c06fa13840bd84e00ffc20881c284e5100020a01c804eb031813a8401082e072c13b4401883118ee15042090c07180630006030bff17fc0000fdd88750cb299f955b0c7902942980000131225fc4c28986130e5230e7e463c09e112742ad063b08ba18e404580838106,
0x118f428a8630833408ec0ad05e502c909060d302648c7800001f403f8031a06100c5818102be05e62dd4506080a131a1f9c0d70c74020e03e817882eb057603300630432092012c825304ae0940127c24b849808f611e83fa0b01000420402258c64037e000455a0a9c13be0da01a004c2027204e826081db1036079c41081f3,
0x106980ad80d7098901f41324219093d092e1fd058080021020112c63c0c64037e000455a0a9c027204e826081db1036079c41081f3188a214c416837109b605bc0b884da0ff820700bd84e00ffc20881c804eb031813a8401082e18ee104857c0c79068013083f9880d180e300c6000c0617fe2ff80001fbb10ea196533f289b,
0x110ee222843a087206bc22e824585da05b427e01a60b7518300ba017300f101e003b807600eb186e284850b848e091a3190001093a18f42be063c8340098404e409d04c103ce311442987f3101a20840b884da0ff8207063b8bff17fc30006038c03180c0000fdd88750cb299f863d8a2a0668260823b07f00188306c4050b75,
0x102be31881a004c206e2136c1be84e10ffc20883fc081603981118468007500e8284850b8073087a30dc000898a18f6079c41081db103607e441981f3105a0d3449c81c0188a214c3fe081c0fe620346018c0617fe2ff860000003f7621d432ca89a52331a809888c7c14c0057c26484d112301fe000088160872073053d8b66,
0x1105c31dc0e907fa1032074c0e007f8102c073022308d000ea01d05090a1700e610f461b8001131431ec0f3882103b6206c0fc883303e620b462288530ff820703f9880d180c300c6000bff17fc0000fdd88750cb2a26948cc6a018fa2aec2af0c6113f00cd016d02e8183e122c247000213e6036006b09fe06bc2be02688368,
0x10cb2a26948c930718fe1e4016d02e805c40b7859d848b091c300c0002ab45134acd48762a77556e10ec63f0334183e12f800107f013e6202806c00d6035c2be04ff043206d00d7803404d709a228080b3015a026224c863e034912720d341a004c2027413041b884db02de13681be84e102f605f027007fe104406302750802,
0x1092e11e80010c7e15f00da01af04d709a205980ad037109b60e402758802105c1fe840c81d3087c1fe040b01cc088c234003a80741424285c039843d186e00044c50c7b03ce20840ed881b03f220cc0f9882d188a214c3fe081c159c0d0026107f3101a235c1a60c7d06fa13843ff0822180e30185ff8bfe18000000fdd8875,
0x1186e284850b8340098404e409d04c106e2136c0b7817109b40df4270817b02f813803ff0822072013ac0c604ea100420b863b8001131431ec0f3882103b6206c0fc883303e6311442987fc10381fcc406882d180e30186000bff17fc0000fdd88750cb2a26948c8c801822157448d89ba153a276824602e805ba03e807a0c29,
0x1098404e409d04c10fe620341b884db02e213683fe081c06fa13843ff0822072013ac401082e18ee31ec6038c0600007eec43a865952303204608855d123626e854e89da09180ba016e80fa01e830a424b847a000431f81af0af809a20da00af8c620fd631fc46b8ace069831f43fc081603981118468007500e801cc21f043d,
0x15232088533fd89a2a5a320c5ab025304fc15704f60b58012609442290453087410e40008b2f1900284850b8c8118f607cc0f381db188a214c40d8821105a1fcc40687fc10382ff86000bff00007eec43a8659190430442ae8b7518182624614834c06d003e806304c91372125c23d07f40004204063c0c64037e31144298340,
0x1165e285c6000c0518042ffc5ff00005136a46537ea67fb134a17948d0c8613b61f6c2d0027000d210e40008b2f142e023c0498c0017fe2ff8000289b52323b41ae11b77190a2d58129827e000107a137ea67fb13509a8dbf8c8418a6094c13f045316b007e40f981e703b6206c410882d106610e4128843a18002ff80000875,
0x11d946dc4644807211e40244221042f190a168012b824000d210e4509009b08b200045978a1718002ffc5ff00005136a46542f1b7e36ee322003907b80884167c2cd825600d210e46000bfe0000a4641108eca36ea321c3dc059f0b36002c6428c84011e09f013b045208a601a421c82510874284804d8459050a0a2022d0001,
0x117fc30000001fbb10eaa26d48ca67fb134a46d33ea6ff087a4c3c646003b000a104433002270a862f8033586620cc8199c3380c04000099fec4d000536fc6df476499611916001400f866007f6288c2a1054317c019ac33106640cce19c060200004dfb62680029b7e36fa3b2533e0c8a0ef416742cc8594180830000000ec6,
0x136fca160764a67d32c032aca970c8f101427003f8089a09761d4409b8a480fce216015b00c208e411c43f40c8206640cd46468c071800300c0001fbb10ea3b1933f952c43a8a16021d8c8e10141fc04e004bc16a00cd03f40c8200007eec43aa67f2a58a9d0646849806e20bd426c8b5916662d500b9813d0ff820703f40c82,
0x102ba298026704c4026e04d03fc07f4097628b440b08100fe007240dd080a0f621da83f609c010a606cc40607f303b0206c0f208210fd032082a2072112f60eb84068002191c0f5440e0c8300d210e40008b2f142e00d45ed0bdc17ba007c5f00223082200ec6020bff180c2ff860000003f7621d544da9194cff6268002a91b,
0x1050a0a2022d03d5190c20706438c8901361164034843900022cbc50b8c06180830005ff8c0518042ff80001fbb10eaa26d48ca6fd4cff626942f1b7e19222d2819e0c1c067e07740fd01f403d006e4406081b104220b441987e819040da04dc80003f7621d533fd89a54ea99f4fdc043d2a5e32400050228044210582060c8c,
0x14dfe7ee021e9310192629ec034006400c410d85b4843904a610e80008b2f142e30005ff0bff0000a26d48cd89a1da03b28dbfc1a850b2324810a8bd708060ff40140020000a323c6480002191c0cc86458c8a0ce0199c33206620cd6276c04507db165609cc0058b291910094421d054317c0000055b8542066a32346418a12,
0x112f6000055b8542066a32346418001165e285c6030bff18002ff80001fbb10eaa26d48ca6fd4cff626942f0c94098829803fa0a2d10201fc00b981710374202826c87c00ed41fb04e0037103ba126017a885810a606cc40607f3101a076040d87fc03c820843f40c8207aa0f4c40e0c0000007eec43aa67fb13454a8a96291b,
0x1101820b400008750caf6268fdb1fb854f4acd821eaab73b3854bc64a8c12169407d00f401b9138003ec405049707301fc01b884ee097613640cd813702ea324c1b409b900040cc86470c9208d40a7c2150330049a08f04e88b561446094c64883d5190c026c22c8a121018208441687fc1038201041a07e8190410e80348439,
0x103b0206c0f20821087401a421c897b00002adc2a10c8d190600045978a17109c213c1be84df02fe32503f40c820ffc20885ff0c00180e300c5ff80003f7621d544da9194dfa99fec4d1311566c10f464b800c054011bc52b0c081806000153a843d3b1c7650ece1d8c3b30438959a9d903b247658ecd0c9616aa2d280fa01b9,
0x1142e2ff86000bff0000a26d48ca85f50b299f464c890214901f9c06000c20186301c6000c0300003b19b8e90ec3b3832605970af004a62d581798c96058e0b14162015f0906133848701370ff01fd025d881610201fc00e481ba10141fb04e00c9516ea29203f380fa05e20bac182030005fc0da024b8498094026e40d9880c,
0x110ea195ca95152c2622acd064d81cf0fd820645a707fa16762ea007d849608f00bd415f8c98098c235c1a681b31018076040d81e410421fa064100c318062ff860300003f7621d4763152a2a587ed8fdc39f954f4a46d59b043b6e3a9bfd59a8c9a01003074224024000ba2cb8217842e15e0094c21d006908722cac0008b2f,
0x116ac030c06100c0193204e02390471191c207021d0069087232341ed884e109e052c46b8c9b190600045978a1712f6000055b854206fa137c0bf8c940fd032083ff0822180e30106030bff18002ff80001fbb10eaa26d48ca6fd4cff6268988843b193820400dd07f40fd824385a501b31018076040d81e4104221384278000,
0x1192c1fc015982b205600abc156880a08ec270064c0a4803ba0c1018002fe192e12800010c9c11ae326c1be84df02fe206c3ff08220fd03208034843912f6000055b8542191a320c0008b2f142e32506000c0617fe2ff80001fbb10eaa26d48ca6fd4cff62689888c9d1934125022980f31908240832b00c4056804d41e989d1,
0x1193e0248048809008a809f013b0069087230005ff00005232088542f9b7e1da06de148dc26a19401108039025514f6002c594843904a210e86438c00180a30085ff000052320884dbf0ed036f06dc0dbe0eca1d983b38dbb0c9f10b00c101bd84a006f830000001fbb2a58a17d0ea1310087aa9e864f0c9913a204dc15a04bb,
0x100007eec43aa89b523299fec4d000550be10f4a97130f3b3a99f46570cb421daacdc65189db011430000000ed21d8c3b4076a0ec86a8632880028c8f0ce0199c2a18be004a610e80008b2f142e30105ff0bff18000000fdd88755136a46533fd89a000a54b933ea858195c32d0658291b32c032b07648ca10134116c3dc8287,
0x152326df87681b78523432903bd059d0b32165800582730fb632886508b2904f209e013b8ca000881c8020a817305e8136424c83710ff82070034843904a2150809a84bb0fe020284e00c8304a610e80330434049410d464c8001165e285c07c0055084c063c2748390095a04603f40c82100420b86020c00180a30085ff8bfe,
0x11372214c0d9880c0fe620340ec081b03c820843ff07e8190410e84bd8000156e15086468c8300022cbc50b83db1928208864e8c07180030185ff8bfe00007eec43aa89b52329bf533fd89a087a3294005826f04dc1f6c6510c850126023c13e027608a4114c034843904a210e80008b2f142e30146010bff17fc3000000289b,
0x12a58875098821d2261c54b865387f0101412ec4e0013516a8000043a86574cff6268a96263c261e329824c0ca305ea2d680660ca408ec092803302b6086a10d0026804c19320338129841e13a221600bf013516661fac09a0131026004b825d8a2d15f011e83e007f0177e067c405017c02f61fb04e004df03d00df464f0368,
0x113a22d5864c8c8e0004329464e83db19283234641897b00002adc2a108531018207041107e8190401a421c8001165e285c6030bfe17fe30000001fbb10eaa26d48ca6fd4cff62686540a60098804d03fa04bb145a20403f807c0037420283b507ec138006cc40607f3101a076040d81e41042000098908750cae99fec4d152a,
0x1142e30146010bff18002ff80001fbb10eaa26d48ca6fd4cfe32a86100b7516b41d9408581070570033052a04a5093e11ec23d0002183e2be044d0b4e03ba07dc0fa01ec03d006e4406081b1042209c41688300fd032086038c03180c0000fdd887552329bf533f90f23b349bfd53a952f19522be06048b4e0372329c65303d3,
0x1180030180000ec654eaacd4ecd2b365674a17d53d2a82087a32ac0058c89190e0a2014289401910116864c8b2b026e298026201340fe812ec51688100f7c1fc00dd019f10141fb04e00ca9191a2d6020b83fe0acc15842af055d0ab815046540853036620303f9880d03b0206c0f208210fd03208034843904a210e80008b2f,
0x10ffc20884000828100420b83f40c82087401a421c8001165e285c2a18be00a82104865501d91036213c6030bff18082ff860000003f7621d544da9194dfa54b10e91fb6261c9bfdcfcaa75566a4c4542c90f23b3432b000602a005640ac0237847614ac326052402eb06240c1c182030005fc126025704a60940235c6040c03,
0x10872094421d0001165e285c6000c0517fe2ff8000289b52329bfd42ca91a195a3268238800219560e401be84e909be06400bf846508b40e1414c828c09c6109820f018400ac013422f88ae0520006402083ef08440fd8208000017941d0c1b8824d09b232480ba82340410022c044045314461f6c13f025304e819583fe081c,
0x101101f6c146025304e832b8144043a00022cbc50b85430a881c845f0054108242ffc5ff0c000000a26d48ca6fd4cfca16d42cc1ae195e327c644877e12802848120005d165c10bc21708f500d210e4128843a165600045978a17180a30005ff8bfe0000a26d48ca85b50b26de0dbf0cae05103290476076704fc25042298069,
0x10fe81fc0408080a037406a43f601d910a606cc40607f3101a076040d87fc1038079041083cc06d00d90269816202d005a426907fa103228843f40c82195430180001fbb10eaa26d48ca6fd2a5c54b137f8cb10004126024702f305cc3018000267e556e9bfd59b1d9b196022bc0268041083c1040000074317940934649008b,
0x102be13383fc0816132006f80f2882100d210e40008b2f142e2ff86000bff000021d432ba89b52329bf533f131150b254ac6598c96058e0b1416202c309062f1017582f10fce300c0001d9a087b1218ece10e26fb8a9d559a8cb20004125c24680fb01e232b0658037109b205d4656813714c00d3019a04c4098a12ec25e0a2d,
0x1087215042090c9908b400045978a1718002ffc5ff00005136a46533f2859835ea46865b0ab3037c1fb00d481b31018076040d81e41042000043aa6fd000c54b8a963b55196a11d459f82c7058a32c82418b7514901f9c17582f1093003e824b8c08180e300060180001d8c766821eab36566a767065a0b2e11ea0a2c22d0caf,
0x1195e057c26707f8102c07243f60cb3026e1fac09704bb145a1fc04050cb5196205a40b4016702cc05940b2016209a41fe840c8a2110a606cc40607f3101a076040d81e410421fa06410069087200045978a17082432a85ff0c0017fe0000fdd88755136a46537e952e2a5832dc4ed808b0fb62da413a08ec012625042290069,
0x103e820b40ee881b180c300c00008750cae99f8a97aab78d447ed948d8cba0fb6328813a0093011e3290229006908722848144045a00022cbc50b8bff18002ff8000289b523299f942f291a19722ad00f981e703b6206c410882d17fc300000008755136a46533f152d19702cb847a828b083a000020b02320454288c64c845a,
0x108a4114c034843904a210e80008b2f142e2ffc6028c0017fc000144da91936fca46865e04a000040c1060c0b4b11ae2d281bd8cb919740d901b4837006f82d380ee81f403d006e465b8cb81954203040d8821105a1fa06410c0618060000fdd88755136a46537e8cbb0930000817a8c181696235c5a5036f037220300f40821,
0x110361fa064100003f7621d533f291b2a5e32fc005828a04b0095c12a845b088402680390251087430146010bfe0000a4641109b7e36e86dc142f8ec9197c1de82ce85990b2c002c139827104e009bc13707db010e01a421c8251087430106000c0518042ffc5ff000051360884dbf3542197a09c43ed8ca41944024c0478767,
0x10ff4204040c8aa2144232fc22b87ce0502090c64f8cae04b032202240442197c0254040007200b432880458c89190e02340450089011032f465e0b7a1970214c0d9880c03b0206c0f208210fd03208034843900022cbc50b85440e4215042020cbb17fe30005ff00003f7621d544da9194cfc33001b20cba06d20dc05a701dd,
0x10288050c0a10141097628b426207f007741fd0405081013802a883f9880d0a862d5c2a0840400004c4843a86574df899fca9621d450b054b8660874503fe0814102020308320fb81f987200000077c0d181ac03b225ec3f601a9103e201c40507fd0fdc1fc026e04b6097605e8096013714c005180b4816802c4131026907f4,
0x106d026e422f8002051e0cc86470c9f195c09606440448088432f804000721912321c651008d01160228044808807aa32f465e08531018206c40e0821104e20b441987e8190401a421c8335191a320c2a08404197600045978a17198030006030bff17fc0000fdd88755136a464dbf0cc2000022444bd87eb194e04dc09a0145,
0x1018611f8246847100009bf153aab35556e10ec66280d708fc307c0010c1c19862be05a701dd03f407d00f401b91018206c410882d10661fa06410541080830180001fbb10ea9bf133faa752a5e33103fa0810098a07041a607e819040000fdd88752a5eacd06618858109c0c245a504a6183807740fd01f403d807a00dc8cc1,
0x10fd800001a601ad1352131412683ba0fe832484080cc113802a8866203d508a4024c53d807600ea01d003980720884094c12d8cc2191a320c5ab8cc017c0150c2a08404197601a421d043900022cbc50b8853036620300ec081b0ff820700f208210ffc20883f40c82180c30005ff0bff00007eec43aa89b5232331860600e9,
0x11122329c3f58134029405140a201430284050425d8a2d09881fc01dd03bb0fe8202840809c01544331064688530fe620342a18b570a8210103f40c8200007eec43aa9184cfe9bf0a960cc719680c0818204a0000433141be84df06d005fc26988eb06e21fe854a84d9103208380128216004e05d40e783fc07f610082008ca7,
0x10e50025404500890110118022a844b000222800d307c703dc078439d082b103e205840988010ffa1fe03fb04e609b81338265018502ec055c0a68c78028c13103fa0810037e075055e81f903ce076c6638b570a821010429880c1036208441987e8190433186020c0117fe2ff860000003f7621d544da67f4df83320000097b,
0x11904301c6018c0600007eec43aa918566a10f533fa6fd2a5a4bfac4d285819941ca004a808a0112022023004550896000445001a60f8e07b80f0873a1056207c40b081310021ff43fc07f609cc137026704ca030a05d80ab814d1018076c40d81e7104207e441981d4180830045ff8bfe1800000043a8657513654b497f8cc9,
0x10002332c4a08c0518002ff85ff80005136a46137ea91a50b23330580843208963000000289b50b2087c66580c316ea11d824182b605962f305ad82bb0570033823d847a159c2be03bd89d1026a0cd025d84bc0fe020280d707f3101a1ff040e0368137205080a20a33028a050c0a3085302822af40a504c40fe820400df87e8,
0x1069a0da04dc8c8d12f6000055b8542180e300060300003f7621d548c2b35087a99fd37e952cb134a1609878cce199415846660a33199205280a301450286050426207f4102006fc55e81db10a6206c3f40c82198c33200001fbb10eaa26d59a843d4cfe54b46668ca2197a1d9c03c025c04a201bc03484530880110421d0439,
0x110140e601b887f80fec1fc027704d9099c132825d819802e205700aa01341018208441687fc1038201041a07e819040da04dc8c8d180c0000fdd8875566a10f533f952cb1344c3466780c316ea11d824182b60596033842c047a15f00e9c5df880a13a205283f60cb5194c05245aa01b31018076040d81e410421fa0641034a,
0x1194e0e9c66708530e4e1fb00d9880c03c820844bd8000156e076040d84bb0fe0202865a8cd0191a0da04dc85420fd032080001fbb10eaa46159a843d4cfe9bf4a96589a50b0334460e01dd03f407d00f401b91018206c410882d1066000043aab35087a99fd55baa75b13454bc6680c2503e807a00dc81ce0e7a270040b0813,
0x1087410e46530c930002057463c014a1998332c26704c419a21fe03fa0a2d102c20403f801c9037420283f60cb519a0333c4bd8000156e2f8039085440a86150842981b310181fcc40681d81036079041087e819040d281a68cc606d026e46640c8d199a30106000bfe17fe0000fdd88755136acd421ea67f25fd62686690137,
0x1087a99fc97f0cd418f0131009a07f4097628b440807f0037420283f609c0036620303f9880d03b0206c0f2082100004c4843a8657523099fca9612fe261c54a8a970cd30442002820609d817ba2f705ed0035003e001433806670cc8198833588a601160224044042e197a01101140a5b00f0094c0378415082c1c805ab0440,
0x1024a04900b70162029a050009c812d024433506468ccd06d026e441387e819040d281a68cc6180e30006030bfe00007eec43aa89b566a10f533f8cd516ea120c08582cb094a30a457c01dd03e807b00f401b919a615982b0855d19a4214c406081b1042209c41687e8190433181b409b9199a301c60300003f7621d544dab35,
0x101f4125c60380005136a46159a843d000c4389bae2a75566c767466b87f8102c133c0e7035e184a2be05a80b4e03ba07e80fa01e80372203040d8821105a20cc3f40c82180c0000fdd8875566a10f6c4d152f19ac042c5ba855d094a120c66801ec05962c7842c081910260eec57c07fa0fec1fd45c084d20994131809f0131,
0x1196a1fcc406816f00004c4843a86575136a460003152e2a584bf89811304260c4c20986130e73f49bf466c89ba01dc27681730bcc0fce335c07d00f4092e104857c0ace08f40ae015d847b180e301860180005136a46159a843d4cfcaadd55a2a75566c3360062072008ec288c15b00ce01f633305ba8c0c09060bd41658498,
0x119b232d43f60aa2037420403fa04c419b405a40b4016702cc05940b2016206d0134826987fa1032288442981b31018076040d87fc1038079041087e81904331866b0541082433546018c0017fc2ffc0001fbb10eaa26d59a843d2a58336c63c014600004c4948c12fe26184c39cfc8cda199805d409b87eb097628b43f8080a,
0x104e009bc13704c4102c332c225844c0fe80730000881015902a7066481bf157a07cc0f381db19b62f802a1854108243354429881b104220b43f40c82198c30106000c0518042ffc5ff00003f7621d544dab35087a33705e18a48196801a421c87e700020bd46658334093005d009b84bb09780dc45e007f009b205c040501ad,
0x119b82ffc5ff0c00180c0000fdd88755136acd533f152d19ba275c0bc8155003e137026500050ffa1fd83a1803c103e204c09504100ce0199c33206620cd607840e304b6000004d44ed845608881fb846684bb0b5a0a00130880702ba1fc000581a5029013384050c8911f433683fc01ae011a022c0450088010c09d01398271,
0x10ff420645db0a2119ba10483f38a4816a011c464c0cde01a811f8165847f198c000866e07e8190430186000c0300007eec43aa89b566a99f866f8001089610e4043006917fe2ff8000289b1d8e337825e03340fe011c44050c98035c0218665844b00022a700f981e703b6206c410882d0fd03208165847f198c035023f0002,
0x10fe81314661834c19c033786630853036620300ec081b03c820843f40c82180030145ff0bff00007eec43aa89b19c233300d701db1014323466f87f009780b2419a08d108e22dd464c0a480fce035016582c7058c0b1416202c3058411f823f800219b8206c3f40c82198c33786018c07180030180001fbb10eaa26d59a8ce0,
0x1101a076040d81e41042150c2a0841200004c4843a8657513499f8a9715224dfa54b067109db011602283bc8cbd00f00970128806f0880110421d0439000204b066584b6026e1fb85e008070976056c0d187f0099c0fb840507f8144208044488cb5102c2d5851180000a8615084c801d9036a25ec2b307ec154406fc0dd0810,
0x12602339421b0065049a1eec4bf809300d2114821c800113a825000f38c0017fc2ffc0003b5a513454b548d29261da43b2142c8ecc7686a0e531e0ce4025c1f6425d8a2d02c405900b2816602ce00009892cd00caea26933f130c72f6b2446718bc002d628b444884d20fe000003fd080a12f6206465a87ec144206cc40607f3,
0x10fe81314661834c10a6203040d8821105a20cc3f9880d169e15042090ce10fd032086000bff17fc0000fdd88754cfcacd067300a508c026bc00089d500002f2867201ee034a20ac40388010fdc139825b0186024620842a081db103607e44198a17186e24fc0f9882d18002ffc5ff000010ea195d44d00064dfa54b548ca859,
0x11032074c4a081db10362ffc6000000262421d432ba89a000c54b542ca6fd000a3b1948c8ce713aa00000008bca11e0339039d01a51056204c40388010fec1fb827304ca096c06200a981280fd6339449f81ae10141fc0671816b02ce05980b2816402c413483fd0819186e285c0e981bf157a07e40f981db19c424e40dd0810,
0x102c805940b3016702d625040ed881b127e07cc4168a1719d0058826907fa1032074c5a7854117fe2ff8000131210ea195d44d00062a5aa16537e8ce90fe813104080cda037e2af4000131210ea195c987152d25fca460674000111e027540d288070fdc12d809407eb19ca2d3c2a08abd02c405900b2816602ce05ac26907fa,
0x13f7621d533f26fc772e33ac3f58128024612d83f70807125e33a467401ae10141fc0671816b02ce05980b2816402c413483fd081903a62af43f9880d169e15042090000262421d432ba89a4cfc54b467500001794339c672073a034a20ac409880710021fd83f704e6099412d80c4015302501fac672880c104207e44198abd,
0x103d006e440608210fd032082a0841219cc30180001fbb10ea99f8a978ced146605880b40146028213103fa08101544059c0b2816b03ac13484ef07fa103233ac3f9880d0ff820705a78541082433a867087e81904214c0001fbb10ea99f937e0cec0004331466b0b50144227742a0841219cc33a867087e81904214c6030000,
0x110ea195d44d152c2a5ced500038cf002d6329c26903cd0ff4206439381cf0fd825ec0000ab7169e15040d9880c03b0206c0f2082100004c4843a8657513499fca96152e4dfa00186778ce302d013483f807fa1014206465a8a2119da33b0675041210a61fcc40687e8190433840001fbb10ea99f86770c180004235c66b0b4e,
0x11036079041087e8190433846770c0017fc2ffc0001fbb10ea54b0a970cf2146605ac0b1014500004c4944d130a26004c10986130e73f2e5ec678816b1466051426904c40ff41fd040c88100f7c073c0dd019f0fd815842ae01ad0a840fdc0d9880c03b0206c0f20821145a1fcc406812e026004d025d87f0101430000001312,
0x10fd032086708cee180c300c0001fbb10ea54b067987ee096c201c09601a312ec25d009b8227044c089411202231466103c4488000036a25ec3f601cf10321fe82690cf1028a01a426204390fe80004408092c186e2a886638b4f0e4215102a18cef0a8233c009a0130025c12ec51687f01014270042981b310181fcc40681d8,
0x119ea04b83f584bb145a1fc040501ae157633a05a787f3101a2af40b1016402ca05980b3816b09a41fe840c81d300004c4843a8657513499fca96d89a19e8123800102e819a01e402f485e70bc615743f300d301a023584f908d311ae2be06620cc311342d380ee81f703e807b00f401b919e43234406081b1042209c4168830,
0x119ea2ff86018c0618002ffc0001fbb0caeb54867b012e0fd612ec51687f01014248412c825804ae095812a8254037410f80e00ce80ac233d00eb016b02ce05980b2816402c40da026904d30ff4000440c898a03a62af40fc81f303ce076c6798cee19c21fa064107f3106620b4410881b101a214c6010bff17fc0000fdd8875,
0x1096e05d422900930004331457702440f9c018013a07db011a2d9c5b48a4902be2a50549855c0002332c57808f5025804dc5300cde19e20494094012319b4053452704dc0ffa207826507f610241398400882a097613383fc081509a404a425b07ee100c1310429834c098a1fd0407833409781fc0404836809a61fe840c07e9,
0x116ce2a505498a4916d2157000088f515e0332c66f015f025804dc6788cda14c029380a681290250049409184e609b8134826704ca098812ec25b0853101c068840287ee100c1fc040487f4101e1fd840907f8102a1fe840c07fd103c200441507e919ea2ffc5ff0c0000007eec32b8cf714960bd417882eb09300dc426c8329,
0x132aa33ec3f00cf817a81fa467a87e819ee0000fdd952c19f432d86578b560ab828f06568af0197807300df81ae034a074c4028808101c205040b8bfe18000000439a91a2a5a33e43ef0c2717a81fa467a87e819ee0000fddab362a5833e04b801dd03b60dc040d04d80ff833d80de8aee04e8091022907db0f9c024c0468060,
0x118002ff85ff8c0118080000fdd995632b833f04ba857e0aea15c85f0002708022fa810b040215dc1d0800007c204881f3803001ee10520ff846f006600d02d9c0e6081415282a4c5958b6914922bc00008b2f0f7e074c40b855c11ea069440281ae10101ce840881b6037e33e840707e919ea30005ff0bff180230100001fbb,
0x13f76657467e800a0b02160048505440e422f801268436004e100401283fb17da33ec3a1021608042bb846f006600d02cac00007c204881f3803001ee10520ff8135844a010a098c222807e16ce2da452481cc10282a505498af000022cbc3df81d3102e07182ae08f5034a20140d708080e7420440db01bf19f420383f48cf5,
0x10b0407fc2a18be0004e100401283fb17d42fb05f68cfb0e8408582010aee11bc01980340b2b00001f0812207ce00c007b841483fe04d611280428263088a01f85b38b691492073040a0a9415262bc00008b2f0f7e074c40b81c60ab823d40d28805035c202039d0811036c06fc67d080e0fd233d46000bfe17fe30046020000,
0x117d4009410b002707f6100820080000f842bb83a1026b04c62378122044a088a01983e7008500fc01a00300b6717c0150c54a0a9316d22cac524855c07fc000447a8af0165e07b80e6073a038c06fc0d701a50f7e074c0db0cfa1052205c40a0811101c202040287e919ea30106008bff18002ff80001fbb19fc004000283f1,
0x14cfe9bf137fa89b5234a46468188b400c0292454a0a9316d21f380008244165e23bc39d01bf035c06943df81d3036c2014404080e1022205c6000bff17fc0002c4d33a44df8987133e08732a5a340839b0cff19fc0000fd48d01156433f800013111a00294067f0000262633fc008000507e215fc0fe0cfc19fa2fb45f60cfb,
0x119bc126007d00fb092e30106008bff180e0000003267f4df898a937fab36566aa96d531843d3b34a26c68309db0114023c3b3807804a201bc65e845208a6110021d043919bc30006028bfe0000a26d48d291836fc0884682800108a6118413f029617fe000131526ff5234a11cdbf8d0408a609f80008cbc12582ffc0000006,
0x1180c000155baa75087a43c944d28583b3a342016584831710303007700ed01d803ac07489da05d032d032f00f401f4125c0010cc5180030186020000b13432b537e2b36556ea95559aaa753b3443c944d1b7e1a0e1ca004a808a011202202300455089600046828d0406220bec255049d021a03f05ba84830596340c17a8cb4,
0x1566aa9e95411d9c556e34285340a561a1010cc000844e049a09d46838d0601f60bc41758bd0092e12600010cc503e007880d801dc18a42f5068101a9034206804e909d91052207440408050a8400a067f0d0018062ffc6030000b13432b533fa6fc4c3898f1315267c4dfeacd84398d09144403b4074847613b40ad81740c07,
0x103c820845660b9e11700db4519036b09b604e40b8833909840de427086e3126405ec09d04c10fe620340be04e00ffc20880b7817309b41ff040e018c09d4200841707e8164830186018c0019fe33f86800d0100016269321a6ff566c21d4a91152c566aa9e95411d9c1a1600085aa8b3b180c300c000589a566caad087910ec,
0x109d413ac27084e009b6136826084c2100820083ff01e40ff807603f981b312f62d9041a082e105a2088410881c1036203440607e91a1228c83f40b24082000f020a8044180c2ff867f0d011a0033fc6018000b13432b4002a6fc4c3898f1321a62a4cf8acd86860cb417a000085740a4819bc0d984f78d0a10362d900d9880c,
0x11598301c6020c0118002ff85ff8c06180633f8000589a4cfe9bf131e26234c5499f155b952a43a4acd553aaa63261c7ed88781d9d556834340630c1308f4000823f82cb1a1607d00f401c10fd806fc0dd08100fe813241a50ab6072e0e381bd836f117029805cf018c06f205f00bd836d06d605cc0b8816f027404e419c84f0,
0x1180e33f86800cff17fc300c6030000b13499fd37e263c4c4698a933e2ab710e654a90e9152f566af05c9871fb63b3a34380880b5a095411d818882b608c43248394007600e801cc03908dc00d209fc221027304e209bc1370251089c10e414b0283049a096c13a82520002195849602c90596120c6060ace15f015080010cc5,
0x107fa109420f841b07ec0fc420184100fd02c900fe0203041408441160230046c004000c0020005000f00220054180633f86800c0600016268cab8cad000a343c52000f901e622c45c38a60145a13083f9880b08f806e468682bf0fe020243fa080f03e020a40010cc5036020205cf0a5f159805bc0b884da0ff820683f40b24,
0x1180633f86800c06000162699d226fc4cfc98f133e261c3b38acdc68882f9148a29b02ea8c0300007670a97843d3b2c76688778d1014d80be45218a5605920b082418a54181829a06870b9e14be2b301b6817302e205bc26d84da0ff8000840d0cc5036007746290bd4073e068c68109d21010201840287e916be22886860415,
0x103d02d9041688210fd2344807d00f405e20bac24b84980fce301c6030cfe1806000137e267e4c78767159b152f566a10f46898bc314ac06c053409d213b220203f38c0319fc3400000267e4c787670a97ab35087a7630ecc08731a242fc05218b411a202f0c52a0a68000433140d80c5217a834084e908080fd22d7c45107e7,
0x117e0035406a00d301a4034406802c9058e0b1816282c405860b0823f047f0004344c3f38d1107dc07f01fc002007e6080c207822307fe00006878542005000145f0057a0afe16142b985760a86300c6000c07180c0002c4d195719547670a97ab351a280b242418b6318181fa850602bb018c235846988d708f611e856701f4,
0x102de13683fe081c0fd220380e08cfe19fe000032ca6fc2a5eacd021d8d1702903368264834a18b40dbc3fa081009b604e426087f3101a05c426d07fc10381fa440701c119fe33f800006594df854bd59a043b3f72345866f09e115f029200748c03180c3000000267e3b38aad08718d1511a821cc438886b10ec220c43f07ea,
0x11a2a04e826087f4100407d03ff01e80ff81fcc4080b64105c20b44110821103820343f4880e0382345042b07e816481f9c68883ee03f80fe001003f30406103c11183ff0000343c2a10028000a2f802bd057f0b0a15cc2bb05431a0030006018c07180c33f8000589a32ae32a8ece152f1a30316462f8d16027413043f9880d,
0x103a60d2c65c01bf1544132040807f514640ce4261013a09821fcc406817b02f813801bc84e10ffc20880c604ea100420b86800cff19fc340400006594df899f8a97130026187ed043a92fe9178346442c0a2e03a81fe8446888213c220643f50951022c12400ea8107020c033007a00d6095a24f424f847a092e12040010d17,
0x103a6288426b08190ff60f3868508d707781fd068c818c06f205f00bd813a06722b6c27504e109c013042610d1507ce20081ee87fe0fe62d904170822101a28c83f3816f02e213681b584db0ff80f583a487e81648340067f8cfe1a0230186018000b1349bf133f1d9c566c54b843a8d1a09ae05983fd03640fd620644880782,
0x1087a43cc68f07820df6300c67f8cfe0000767421e930f21e634745bd000119782cbc50b8c0017fe2ff800026fc4cfca46948ca89b1a382f5068107e91a34346068883ff0050103c11183f304060fe001003ee0000343c0028be00af415fc2c285730aec150c2a101fc00016268cab8caa3b38346c264834814c024403c10367,
0x10001626937e267e4c787674a9521d25922b54487912fe261c7ee544d8d20049a324847a8cde128028481a5032706640d9818204c90f0c12f826b88b2029004a809a81690f041fa059207ee100c1fc040487f4101e1fe840c0c0017fe33f8000589a4df899f931e261c3b3a21cca97843d261e347c68e8acc19fc300c0001d9d,
0x100d210e4000892e186e0aa816587d20906240c60600f001da03a44ed0d0805d034780010cc518002ffc5ff0c06180e0002c4d26fc4cf89870eceaab754aaacd553aa89a1a422980264813402660d2825f0b7a066401bc21b0439160200043ed844c04e8093432b036405cc0d9c17487e81648340067f8c0017fc2ffc6020cfe,
0x117a80e7c0d18d0213a4276440e8808100c20143f40b2418002ff85ff8c0419fc30186018000b134ce9137e267e4c7899f137f261c4c4476744398d23146e05a00a3014109ae13241b2034806d80cec3fa080f0ff4206067f80000cb29bf133f267c4dfc21cc97f130e3f6e348845a006000ea1f382210a931528091012d88f5,
0x109b61ff040e00cc05ea126007a0c0c018c11e85b200fa092e22886030c07180633f800006594df899f8ece8875087a54b869200fc1818127424180c305f60b2c23b045716f40ad804a806f086c29ec21c8b01011a022c0450089011000043ed844c050409d012686561a440b981748d211a3e297c68f0002198a07880d80c52,
0x10672130809c813a09821fcc406816f02e213681b584db0ff820700bd817c09c00de427087fe104406302750802105c300c67f8cfe1a0034045ff0c00180c301c00006594df899f931f1d9d10ea10f469282e813b431d068e08ba0596235846988d709060f9c1ee83bc1a321d24411082e027213043f9880d02de05c426d036b,
0x119fc340400006594cfc7ec897f130a26004c30fda130226107ec09822cd33f70349836e87eb11701e0845c87f80fe8205840801ce0382123024182dd05962b2065c82e813b431d007288ba0fd40c6008b0304020e041825704ad0940127c0fa01e81a48303007d00f405ea03300630497093011e868f0a32104220b45b208a2,
0x1b134655c6550d28142c29bc69307fa142e206416581d508fe306046b8d1703d020845b20339098404e409d04c10fe620340b7817109b40dac26d87fc103805ec0be04e006f213843ff0822031813a8401082e18002ffc5ff0c06180633f800006594df899f8ece8875087654bc69384d702cc0d903f588b80f0428c86800cff,
0x1907c76746948cb813ba288440c82cb079c11fc60c08d707ba0ef068c87491a4e0008692836b02e205bc09c84db09b413043fe07f316c8208840e080d0fd2348c68d841808140fb820a03f807e6103c1ff80001a1e011c0140020000a15082a18be00fd02c900fe0203043c088c11485730aec15e82bf8585180c300c67f0000]

def cP_2 : List Nat := [
0x11a2e000849e81d503e807a068d0d29103222885b2082d10421fa440c07e8164830186018cfe0001626937e267e4c7c4bf898613003f6920f869502cb189a11fc0f981e703b60ef05108d190e92349c0010d25103620844168b6410321fcc40687fc10381fa440c0cfe19fe300c60300000cb29bf133f263e25fc4c309801fb4,
0x101e003b80768c1f091c12346960d2b0fd02c903f38cfe1806301c000589a4df899fa41f9d9c087634b446882c9058e0b1816282c4058630305a0847f08fc2b3868b8b640e921fa41e709d90fce300c6030cfe0000196537e483f3b3810ec8712ab61a5833784f0848d149003a46018c00000099f8ece043b21c634ac60c08d7,
0x10fce300c67f00004cfc98f0ece043d2a5eaadc87110f010e634c05bd00010f7e23d4521073a037e074c0db01ae034a2f5040b8811101c202040287e91a5c2ff85ff8c0000009bf133f589a3b3854b86978d1a1144300c67f0000b1349bf133f1d9c2a5c21d46970d1a0fd212544e902f01a2e11ac4fc0ae81818240c5b282e6,
0x1907e767069a0a681a641fa46988cfe1a00000133f263c3b3810f4a97aab71a6628f40660bc30bc217702ed80cd1a601f9c4e901b01010070440707e91a62300c67f00004cfc98f0ece043d2a5eaadc8710d32127a07d04510b64105a300c67f00004cfc767021e952f556e21d46988a431a202f0c52a01c1036027484070808,
0x14cfc98f8ece952f10ea34d4517088d11041fa84a88116020e041809d07f4095a127c26088581020345440101f40ffc07a03fe07f303a803e80e08b64105c20b44110821103820344f080ef01d4125c68987e909202d7c4ec81d51a66215869780021a5a1f9c3f40b240ff430006018c071a0033f86030000b1349bf133f263c,
0x114f610e4046808b0114022404400010fb6113014102740cac2e786910d1f1a3c0b9800102e9198a34840f101c10360068c4e909d9103a203840408050fd234d43f40b24079834d06000bfe17fe301067f0c03180c0002c4d26fc4cfc98f931e267c4dfc987131112fe26184c0241f952f1a6c00086938d25180c000032ca6fc,
0x107ba349068c8b6410441fa469b83ce0e9234d869a0d2a0fd02c906030cfe18060002c4d26fc4cfc98f931e267c4dfc987131112fe26184c00fda0d3800022de847a8b2f0f7e06b80d2873a037e074c0db0bd4102e20444070808100a2ffc6000bfe00009bf133f152e10e634dc07e0c0c093a120c17d82cb08ae2de804a806f,
0x1103834d01e087fc0ff61fdc26d04d502aa13300a781320de805bc0b1814e025c048c51907e8164833f86808cff1a00300c000589a4df899f931e267c4c3c9bf930e12fe260234e869b0d3710301fa440e07fc09b60dac69c07e8164833f8000589a4df899f931f263c4cf89bf930e262225fc4c309800d391830235c00103bc,
0x10fd21fd44990148098e050c0a1013a0264049837d08421082210041f8147027604d00948d391a7428c83f40b2419fc34046018d0019fe0002c4d26fc4cfc98f931e267c4c3c9bf930e262225fc34ec3f6832d064a0c8c69004be1a421e183fa01c10fe006c03f701a31a4423f069b89d213b2203c40708091010201840287e9,
0x1000054bc43992ff1a7a297c69b87e9126404c40950128024e049409201230de604b40910d3b08300fb8209840607f20fcc204840f08001fa059201fc040608281088218044600d402180461a5033f86800cff18060002c4d1957000634f06900d210fda34d00e087f00360068c6910d3713a4276440c080e1012202040283ba,
0x126107eca2f0930c26147ec235093041a80000452d8ccb06cc0c9c19907ed06a4135c2668786108005a00aa012914641fb840307f610241fe840c032d065e2ffc5ff0c0019fc340467f80000cb299f530f08733f6517849868d3f0fd604d009981310260340067f800025fc4c0098713022610e4e469f0a5f0de633f86018cff,
0x1100c1fd040787f610241fe040a87fa10300cb41978d3f097c34f83f8080911f82ff86000cfe1a0233fc68000000cb29bf533ea61e4cfc21cc97f1300261c4c08984130a1a8211680008c99195e22ec1b3035c09ae13441a5033202cc056869307eb065e2ffc6000d0019fe000032ca6fd4cfa99f9649acd325fc4c009871302,
0x10fe020243fa080f0388102001782180fec2048400882a000424d80e4081113b210440000d3c0a84088c01d8d280360202069e8c0417fe2ff86000cfe1a0233fc6800c06180e300c000589a32ae54bc43990f226004c3898113081a842bc01b3032706940cc83f6835209ae13343c3016502a004946a004c91472298051907ee,
0x1007634a00d8080818082ff85ff8c0019fc34046030c07180633fc000589a32ae54bc43990f2261c4c246a1829608c2195800082be148211ec1c4032706940cc80dc87ed10160d483f984e8099a13243c30a2d107a06200a9814602503504197832d097c34f847e0a320fd02c90200802707f6007c212823600a621543f70806,
0x119fc340400006594cfa987843993031a88094c32b043a060400042500b2f142e07a01b3034a10401fb43ff0352064a0c9027004d7099a13243c3083a107205f00b38152028a049c51907e816480fec00f841f046021543f708060fe8203c0e20408005e08603fb08120ff420600010936039020444ec8411000034f02a10223,
0x10000196537ea67d4c7c99f9321a7032a5e21cc879130f1a8c35086a18d44081000bc10c03fb000034f02a1001f1a501fa05920cfe00016268cab952f10e643c8980130e1a8a2bc01990366064e0d2851c0352064a0c9026b84cd099212f83c30164029e050809781240fdc20183f808090fe8203c3fb08120ff420605ff0c00,
0x11806340467f8c0700016268cab952f10e643c86a382cb090632bc5ba8a270216129446b845a159c07b00f400010e7a06e441308201176202c40007fe06b80d983f984e409c0134426b8304116422dc0c1817e02ba05a4528878213a4070440707f8102a1fe840c0002126c072040889d9036020206038cfe180630185ff8c00,
0x109d0136826484be0f0c1b9437006d30da006180b78141025c048c47e0d451a8635185190401004e103001a821e083e08c02110233084a08d802987ee100c1fc040481c1101c1fd040788011054000849b01c8102227642088223007606c04040d44081000bc10c03fb000034f02a1001f1a501fa05920c0619fc34005ff0c00,
0x1092e126023d047b0dd01b8c6018cff19fc301c000267d5568acd953d2a823f7243c898390f0087a352468e8acc0f2017a42f385e31a8e000849b01c80360276440888080822000069e0542044600ec6940cfe180630186038000b134655ca9788731a9027681740a6801d22bc056b834a06640c9c0ee88fe10340e1c3fe0323,
0x1100420b80be013a02f613801b584db027a05bc09c84c102e213683fe081c067213083f9880d06f213843ff08220fd02c900fa082d03d020844510b640fd235201fd80001a78150800f8d2817fe2ff86020c06180633f86808cff1a000002c4d19572a5e76746a506de16c61fa85ad0116020c03d017880c6057c0aec256849f,
0x103e81ff80f407fc0fe625ec4510b64105c20b44110821103820343f48d4814641fa059203fb003e10440000d3c0a84088c01d8d28180633f867f8c061a003404000589a32ae54bc6a589ef091c0d98174044c000210e813a02530cac0af815f8411044600ec20f823010aa25ec0010d49173c24c856608b8067828c80c604ea,
0x11044207040687e816480fec0000d3c0a84007c69407491a962b3067f0c061806340067f8000b134655c98713003f724c0897f130410ea35303fa04c9102028240e08c5a15d034546a500021a921b8c1b78a60173c24c856608b803180de40be017b06d605c40b7813d027404e419e033909d4138427004db09b413042610802,
0x104600df827107ff104a1fa46a68d4b07f6000069e0542003e34a03f40b2419fc340467f8000b134655c98712fe2600353857801ae034a06fc0e98bd4102e2038404080517fc3000000267d2a5c21cc6a68c5c0fee1fbc00104cc097235240a88126173c1fac0be01710274138026d04c107ce0f743ff07fc0fe622885b2082e,
0x1261e000ca970cab1aa20d98547078219fc000032c930f43ae99f944d0d50027a353809c816f09b413043fe07f3103820343f48d4d1a960fec0000d3c003e34a02a107e8164833f8000589a32ae353c45c0d4c14640dac26d8379031806342750802105c04e826087f3101a05c426d07fc103805ec270037a09c21ff8411041f,
0x107da16202c38586009600e4016801d002a25d4002820e080a0fe83f080240046008801080200a8615103908be01a9e0002c4d12fe4cf89bf80018caa664a35480e60aa9102c1fe0268835c159035400ae840e081200ec01a836f09b61ff040e037b09c21ff8411038e0f0413ac401082e0e922ff86000cfe1806000032c8875,
0x1031e13a8401082e03061390400082802fc13803ff08220fd02c902a10c0319fc0002c4d0875261e54b86aa0a7a069431585ab013d09821fcc406817309b40dbc26d87fc10380dec27087fe10440e382758802105c0e5c3c104f0100820d03f40b2419fc0002c4d0875261e54b933f8d53081e089c69d800a083010241ff83f2,
0x1100420b80f40821098e05240950cfe180630186040c05180430005ff8bfe0000196443a930f2a5e99f937ea63e72709871c8d291851363554002802c005600a8014802807fe29e81a50cb91aa0354c0128d521aa21d242a18be002720dbc26d837b0f04138400007d0032613b0401883102e613683fe081c027a13043f9880d,
0x1093011e840980020fec289426681a706a6201c22207ee04c21e180d8000b064e202864488fa039c1fc0044027404e609c4138026f04dc205825f044b08981fe019900011172333054e0ac819bc20305b208a2027204e826087f3101a05bc0b884da02f605f0270018c09d40dbc26d87fc10380dec27087fe10440e383c104eb,
0x109d42008417036f0f04136c3fe081c17fc30005ff8c071a0033fc6018c0619fc000032c8875261e54bd33f26fd4c78a2686ab88ba01e8033024b847a01e003b807600eb000429b824708a215f0277c1b3078216c8301c6030cfe1806000032c8875261e99f937ea89a880c35585138a2f020e03e817882eb01981cf424f8497,
0x1101a063c2750802105c060c2720800105005f827007fe10441fa059205421aa833f8000589a10ea4c3d33f26fd1ab02d984a0887410e4221019908ba145417683f809f810142dd40d800f001dc03b00758c1f091a0d700010a761a661f9c17402e61aac2be04ef836616c804e426087f3101a05bc26d017b09c01ff8411018c,
0x106de136c3fe081c06f613843ff0822071c13ac401082e0374070440807f409920d283c101481ab01fa05920d54180c33f86000bff17fc300c000589a10ea4c3d33f2918513635646aa8cb91aae05541f701350fc408045e508cd0e4a288c1b784db06f61e0827080000fa0064c2760803106205cc26d07fc103804f426087f3,
0x100040b2c1740c1816962be04ef83661ab2235846b88d3159c070440807f409920d283f40b2416c822883c101e8104207d06aa082d029035606038c06180633f8000589a10ea4c3d33f29181ab406c066c080a092200083f802e91a4e12f869a0135145023e8199008804e8332c225844c0ff6000426b0a9c06ce33785b208a2,
0x117fc300c000589a10ea4c3d44d043d1ab8276845d02e8022c041c08300fa01e8033069884ad093e125c23d000218b6074c57c01d613be0d9865c8d5a16c822883f9880d06de136c3fe081c06f61e0827087fe10441fa059201e8104207d06aa082d180c301c67f8cfe18060002c4d0875261e99f86ad80d0117403c024189da,
0x11144070440807f409920d2862b014816ac06c040507f0097c0cc84c0809501281154548800113140e38275839709e0201041a037b09c20dbc26d8782026a26a46ad854300001f400c984ec100620c40b984da0ff8207009e84c10fe620340c784ea100420b80c184e4100020a00bf04e00ffc20883f40b240a84355067f0bff,
0x11062063c275018309c82000414017e09c0150846b81c110201fd0264834a18ac0dec27087fe10440dbc26d839709e0201041a038e09d62008417078202902d586ad817309b41ff040e013d09821fcc40687e8164807a06aa0821180c33f85ff8bfe0001626843a930f5134357465a02e71826124407d00c619a0125c23d0b64,
0x1261e357c6960a4816760b2c623047f08fc2d9026087f3101a13683fe081c09c01ff841104e4100020a02750802105c13b040188311800300c67f00000cb221d533fa6fc523120fd59a90ec1d8c10ec6af0c98142a11c40010d5c036020283f804be0664260404a809408aa2a44000898a026a26a42a180000fa0064c2760803,
0x113dc2d543f38c1301f403d0063049708f400086af0cde1aba235846b88d3159c070440807f409921fec1a504d5029031580b50b561ab607d00f40d54072e0e381bd836f02e604f43c10821105a2d9045104c10fe6203426d04db0ff8207027087fe104413ac401082e09e0201041a07e81648301c67f0c03180c0002c4d0875,
0x106d6136c1bc84e1057611ec178849816b41fa8063047a16c81ba037187eb02f604e80be04e00ffc20880c604ea100420b8083049f03d0208408b04ad03e820b407a049711442e780b7817109b41ff040e013909821fcc40687e816482b306af8c0019fc34046018cff180e3400000589a10ea54bd33fa89b087a76706b007ea,
0x106d6136c1bc84e1159824445cf06e80dc61fac6af817b027405f027007fe104405c40b784da0ff820700c604ea100420b809c84c10fe620343f40b2403d020840fa082d19fc34046018cff180e3400000589a10ea54bd33fa89b087a35843fa0a2b102024405ab01c10db20bcc15f0b55111a22084a88b6313dc28c819c84c2,
0x108e22ba05ad0a3216c80ce42610139027413043f9880d02de05c426d036b09b61ff040e017b02f813801bc84e10ffc20880c604ea100420b842b8cfe19fe34046018c070000196443a90f221e0e4e087710ec2a5ea26c21d9d9d21c435883f686dd0dbc35803f50116020c03d006304ad093e125c23d0a3216c8228819c84c2,
0x109c01ff8411017102de13683fe081c031813a8401082e027213043f9880d0fd02c900010d6119fc34046030cff18063400000589a10ea54bd33fa89b3b3a359068b8d5e1998316c50a836f0fe6203426d87fc1038337867f80000cb221d5c9c10ec2a5e99fd44d843b3b3b20fca961fb91ac6333062d0a1506de24404fd0d17,
0x10fd02c9042b8cfe19fe34046018c00180c3400000589a10ea54bd33fa89b1aca00003e507d006b60e4c1c6838206f40db419e07ed1ac613443fc081603a820640e701d509142be00710d620a8428c85b204e5100020a027584ed100620c419c84c206d6136c1bc84e1159824445cf0d3e02b41ba037187eb1abe05ec09d017c,
0x1103833fc6018cfe0000196443a90f273f0e5e8876152f513410ecfdc8d6606943168264836f0fe8244040809fa0382345c2388ae8193029206b200021ac233785190b64067213081b584db06f213845660b9e14c034f837187eb1abe05ec09d017c09c01ff8411017102de13683fe081c031813a8401082e027213043f9880d,
0x1067213081b584db06f213845660911173c29800ad01660dc61fac6af817b027405f027007fe104405c40b784da0ff820700c604ea100420b809c84c10fe620343f40b241aca300c67f0cff1a023400000589a10ea54bd33f843b1ace1fd026488100694070462d8b3b03a6075440c87fa09ae0d981b78b640fe6203426d87fc,
0x103e820b467f0c03181033fc6808c07180c3400000589a10ea54bd33f8d6900181b6436e85cd181033f86018cff00004c1c21e9d8a3b2c7630ecc1d8e3b2876408759fb71ad01fe0268881606b607383e5048a000003883e80ae807260e341c1037a06da0cf062c87ed18be35982a10a3216c81394400082809d613b44018831,
0x1122035a02e687ea0624045818002fe020c03d0178893e018c0aec15c04ae095a128024f8497093011e823d80021ace28c85b208a209d613c04020834067213081b584db06f213845660b9e14c01ba037187eb1abe05ec09d017c09c01ff8411017102de13683fe081c031813a8401082e027213043f9880d0fd02c900f40821,
0x116c822882758339098404e409d04c10fe620340b7817109b40dac26d87fc103805ec0be04e006f213843ff0822031813a8401082e02b41ba037181e8104207d04168bfe1800300c67f8cfe1a02301c000065910ea43c898390f02a5e99f821e8d6a0fe81324408034a0382314c68502f313dc003036f0d49072e0e381bd836f,
0x116c8136c3fe081c09c21ff841104eb100420b86018bff17fc300067f00000cb221d487910f073f0e4e1cbd10ec2a5e99f821d9fb91ad613443fc035c102c2b200e709e1145e24f436f038e06f60dbc488046e1ad002d83f508ba0624045818002fe020c03d0178893e018c0aec15c04ae095a128024f8497093011e823d8a32,
0x11a4c317c6b580021ad435a45b2033909840dac26d837909c22b305cf0a601a7c059837187eb1abe05ec09d017c09c01ff8411017102de13683fe081c031813a8401082e027213043f9880d0fd02c906018cfe19fe30186800000b13421d4a978d6c03822ba04080d150fe828542648ccb0694000465c8a9c1acc0e381bd836f,
0x10e9235b03fb87ef099812e437186e802a204985cf07eb1598357c0c6037902f805ec1b5817102de04e809c833909d4138427004db09b4130426108020ffc07903fe01d80fe606cc4510b64105c20b441108211038206c406880c14641fa05920c00180e300c67f8cfe1a0230186800000b13421d46b681d510322cec3fd0c59,
0x10002332c5ff0bff0000a16548ca85b513699f46b787fc09b620681b781db19f21fa059207e91ada33f8000589a3f7254b46b707ec035806a43c0880a0fe20ea023b02b4114e0bcc5b186de122035a03f30b5a0624045818002fe020c03d0178893e018c0aec15c04ae095a128024f8497093011e823d800207420f9c1ee8c5c,
0x110300d70268815a0ff020541a504c902881fd04078332097c04c43f40b240fe020246b707e91ada30005ff8c06180e300c67f8cfe17fc0002c4d043d21d87ee487910f0260e76688710d7114ac29a015e82bf05780ae44e90c5203602f504040c0319fc34005ff000010e610f4a96267c880a35c01440cae08b4094c64c843a,
0x10ff020541a504c902881fd04078332097c04c43f40b240fe020243f48d6d18002ffc67f0d0017fc0002c4d043d3f724c1c8718d7203ba126040d02f50ff80db826d8a98152829241550a1212801f485b483041206241045906de179827644e9033d18a406c05ea08080dd033780008ccb05700aec6b80d6f06cc135c0b307fa,
0x10fd02c904ec89d20fe020243fa080f0ff020543fd081818a406c05ea0d6e10101fa46b68c03180e33fc67f0000b13410f48761fb921e443c09838d73088401d012d8a9819082da465c8453197825041b702f51424250024c030403ba22c84588a6801e60cf45ea0d6e087400046658d6f06cc135c0b307fa10300d70268815a,
0x117a820203f48d6d1806301c67f0000b13410f4a9610f221e0766d37f267c21c435d426d87fc06de20686568bd00fd02c900d001a1100a06a440407e91ada35b867f0000b13410f4fdc9d9b5232a26d42ca6ff1ae828fc16482b4090611d86b88b7516b435c86b7836606b80d2819904d709a2132425f06e802cc05680a20131,
0x11aea35d81790d74165635b866f0251087400045978a17180a30085ff8c0017fc0002c4d043d3f7243c88781d9b5232a26d42c8d77190c0c1016482e605ea22c816609da14d003a43f40b2413b22f506b707e91ada301867f0d0018060002c4d043d3f72766d48ca89b890c438c6bb02c91446120c51d0b750a84276462901b0,
0x1191013a065f00a6030e29ec6448c870fd6023404500890110294465e82bf04a60af83f40b2413a420044150bd41adc1fa46b68cde087210e80008b2f142e30006800cff17fc2ffc6018cfe0001626821e9fb926144c1898012fe2618766d48ca89b1da06de098113044cfa35e00058288050a32246438c8808b425001298c99,
0x11aee000459787e816481fc040487e91ada35b850b8bff18002ff867f0000b13410f4fdc90f2261443c0983130025fc4c30ecda919513635e813f045319780dbc26d87fc10342f403f40b240340068440281a910101fa46b68d6e00022cbc50b8bff18002ff867f0000b13410f4fdc9d9b5232a26d37f8d79052a118864f8388,
0x1b13410f4fdc90f2261443c0983130025fc4c30ecd8d7c09060b245ba8a5314d00ba017387eb0fb2059c0b2816409ae0d983f40b2413a41fe840c0bd418a435b83f48d6d180e33f86800cff18060002c4d043d3f7243c898510f0260c4c0097f130c3b36a2686bd8d761aea0bc86bc8d78026004bc1250066097c10d421a0332,
0x1087a43c88711d971b042410600000021e443c08770ec6566a43a88761d9d54eaa9548711b7e1b021f9c60180003b3843cc6c00a4f19fc000043986571afe27486018cfe000021cd52a0d7e13b2300c67f000010e6aad86be82ca0596052052d0a6009920d286bd0d7b0fd02c903fa080f17a835b83f48d6d19fc340067f8000,
0x13b307668ecb1d8c3b3843bc6c389bd1806000021eaab73b3843888791d963b3443c087610ee21c836183f50c07000043c887810e621d4438887610ee21c843a06c28a561806000153aaa55087a766159a9d9a3b184388ece0d841486300c00010f03b2c10f4ecd2a7521dcacd48792a5521c476706c18a541806000153aaa55,
0x13b147630ec91d9a3b307670ecb10ed1b181dc4601800054aa10f4ecd1d8a3b3876588768d8b13c4301867f0cff1a00000043a8657260c4c08982130825fc4c38a97930c3f6636283f58cff1a00000097f130426004c30983130a26044c209870d89146633fc680000025fc4c00986130426104c2898739f91b1029146018000,
0x154ab0e91b7e0d930de433fc6018cfe00004c34ece9fb721e2364847e0d0019fe0000439865926044c389841fb31b2228c867f80000cb27eac6c80a5a19fc0000439952f087a4c3cece39f91b1e2650601800021e043c887710e43b1636383ec8cff00004c18981130826144c1097f130c51344c0133f397b1b1a26e06018000,
0x11206301c00010f221c443a9b7e8d9a0f4a301c00010e421c443c887536fd1b321cf46030000766e54bddca10e31b302888603800021e443a8871371d6ebe365c4dd0c07000043c087110ee21d843c8872375f1b2c2408603800021c443c087910ec21dc43a9b8e8d9510b0300068000003f708750ece152c1b281f486030000,
0x125fc7ed8fdc0da411ea3000000291950b23b18dbf28391b46285c5ff0bff0000a4647698da200043018000043c0874368421c8bfe00000885aa08da00e742ffc0003b94766e54b47638d9f036c2ff8000152d772a36785208c0017fc000142c8221523299f541c8d9d067a2ff800046213f7236700008bff000008781100d9b,
0x136e86dc0dbf1b7c36e436a84e98c0319fc000153daa541b521f6c5ff8000513707a9aa10da814922ffc000291904426dfd42ca67c50723b246d389761800000133fa9191d903b1944d283950b236983f68d0119fc0000fd51fb23f5c7ec0fda1fb63f7036944880d0119fc0000fd91fb426144c10fd8130c26044c009841faa,
0x11da836c03e28c011808000010f8eca1d903b30763284750b636bc4530c0000003b207690ed01d983b2876a34e01b5c22d060000001d8c3b207670ecc1d943b51a708dad14de30000001d9d1da410ec32c9fb952323b506d608dc18000000dbe02214df8a464db91b7a36f06dd0db80ecf1b56002c6010c0500006dd8dbc1b7a,
0x1000120f555a2a741b6e292060000001d8c438cece0db60d8e33f867f8c030000438c97f9d9d3f6a36d415f8bfe00011014ece8db40e9233f8601800043ac54b86d98728180230100000ece1d8c3b207650ecc69de36c84790c0000003b187640eca36fc3b3876628391b6200186008c0400003b187690eca1da03b387640ecc,
0x117fc000148ca8594df8a16d48d28391b801e0867f00003f704c3c6df8a3f1806000155b90f04dfaa95421ea67c21c4766c877263d1b7c177060180003b1a43c46de85d518060000ec690ef1b78173c60180003b1a43b46dd85c118060000ec690e51b74178460180003b2e43c46dc85da18060000ecb90ef1b701e006018cfe,
0x12602aad96698dc90dd633fc67f0c0300004c048788dc80dc033fc67f0c0300004c048768dc70da633f867f8c0300004c048748dc60da033fc67f0c0300004c048738dc50dca33fc67f0c0300004c048778dc413dc300c67f0000087a43acece267f556c370c2ed8c030000762c8788dc20b9c300c0001d8b21da370451e0c00,
0x100004c0c8768dd013e4300c0002b355504ab0955a2a7a4cfeace959b2ab75134df7137e8dcf0ba4300c0001d9321da37383630cfe19fe300c00012ff21c67674fd88dcd0d9033f867f8c0300004bfcece90e33f6e37303628cfe19fe300c00012ff21c67674fd78dcb0dbe33fc67f0c03000043b497f8dca13c833f80000657,
0x110fe30000001d9c21ca3b446ec887718000000ece0ecf21ca37604420c000000767076990e51bae21c860000003b3843947658dd610e830000001d9c1d9a43946ea89da180c000155bb75e880c37504510cfe1806000043aab371ba6234c6030000566aa9e88738dd20dc633fc67f0c0300004c1c8768dd10dc233fc67f0c03,
0x150b2a1787658de111563000000022136e86dc8dbb152d36e06df9a8035c01bc01cfc5ff80005234a0e47648ddf13f0300c0002ab721e4767021d9d966fb876686ef08bb1800000144da67e043ea16c6ee89af1800000076328595232087d41c8ddc08742ff8000022183d2376c45a8c03000054a88792838874920f62030dda,
0x110e610f4a97930d1bd4296c6000bfe0000a26c110a8594cfaa0e46f488d6180c000159aaa8221d237a03e70bff0000d38141cc1881bce16c8600000036ee3b546f305b418000000dbd8ed51bca23fc600000052323b1942f28595072990c6f2074017fe000141ca85e1d96378c5090bff0000a46542f0ed11bc425005ff8000,
0x10000aadd33f152f5134767541f0df014f630000000ece1d903b4076535401d983b506f78a7819fc00007650ecc0cb318809878ed01d90a4647670ed41bdc29c06018cfe000043c821e952f6ebf0ea86f68a681a0033f8000043d2a5e21cc8719d9c1bd8298067f8d0000004bf8986130a261ce7e46f58a5e19fc0000ece1fb2,
0x10cae4c146fb8ad319fc300c00010f2566a438887310ec21dc43a032b93031bec2b446030cfe000054bc987065721c637d45670c060000acd555a10ef1be82b306018cfe00004c388798df31530300000046a21da03b20765462004427ee47670ecc1be42a4c5ff800052326dfc110a67cb134a16541c8ecb1be22a0c6018cfe,
0x12a5e43c46fe8adf180633f8000152f261c195c8768dfc15bc33f8601800021d4195c87610f02a5e4c388770dfb15ba33f8000152f08764bf898737dc0caedc706fd0adb180633f800010f225fe43886fc8ad7180633f800010e2566cacd487310ec21d043c887713011bf02b5867f0c03000043c959a90e221cc43b087710e8,
0x11c0a2cbc600000051363b4948c821f1c082ca4600000036fc6de8dbb0ed51c062c9067f0000b134195c7010af8180c000155baab421c638045780c0017fc000144da859523299f541c8e0015d0300c00010f021e4aad021d90ec566a43886ff8ae119fc301800012fe2a5e4c3832b90ef1bfc2b806018cfe000043a89870657,
0x119fc000155aaa741c182d906018cfe0000aad443a8e0b16be300c67f0000566eaad87050b5a180e000087110f221d843b9b8e8e091682300c00010f221c443b8ec68e081680300c0001d8c087aacd4ec91d98556e99f4ece2ab41c0e2cec6018000556843b155b90f20876acd47030b3417fc000142ca9194cff626810fa6fd,
0x126141964fdc46a11c222de8600000004426dfc769289b52329bf133f0e1016ea301c00010f021e4df748710e0f16d4301c5ff0000b13443c9d9ba89b52324388ecb28392a5aa16d42c9d9c3b2438385b40c0717fc00008762919b13454b544d9b7f3b3843c1d9b90e24cf83b207660eca0442a0e4879285b1d9c38345b28c03,
0x118000000fdc2a6310e643c942ca92621d010f4ece90e450bce4f8873291a21dc43b0763285b2a58a26c87826434df8acd470a0b8a180000007652a63087a6df948d022121e0439887410ec21dc439076310f23b3aacd541c29261c262e1c67f00005aa21964985462025fce7e0fdc2ab51c242e1867f00008c4021cc98612fe,
0x1175c301c00010f22a5e21cc21d90e21c322e786018cfe00004bf89861300261c43c470c0b9d19fc3018000087321c499f0a9790eeb13443c933f9d9b4dfcacdc70b8b9619fc000043a952c4cfe195ca970e16171a300000010e41d8cacd487310e821e0a16d493291a21dc43b0110843d50bc767553190f2523c990c70a8b8c,
0x11c4033a067f800010ea195c97f152d261ca46070f8cda19fe000097f130c52304c39cfc8e1e18f033fc000130c52304bf8985130e73f2387462d0cff19fc000032cad5259a0a46421d952f10eaa46959a0e1c17e0300c0001d963b3876688789d8c1c362f306018000556e7668ec510f2087a76588772b3554ea4388ece0e1a,
0x1190c000142f289bb134a46537ea91a1c42097068284411b3637744e88135097c0cc8666013d05ea130424c07f303ba0ba016e880b116237502460d9801e603a40710e0f09060b2c0a40d8f1bd613241a507e81c0420446be87f010121fd04078c52039c2f506b708140fd235b4000589a087a7ee4879130a21e04bf89862918,
0x13b3476707120df200e836ac221027c011e096c22984521c4232f01b70e221912321c14402850136116822c8de2060822c83f40e021b382f506b707e91ada33781288ddb1b3638106d10000b13410f4fdca91951367674711881a03ba1ff024c04db05ea0dbc3f40e0217a835b83f48d6d0001626821e9fb93b3aa46c7110cb9,
0x100b8018402c8da60554364c6cd0d8901da03a46c6816702ca05906f08dd409ae378868402e8186e0d981820e23116438907100d7c0fd038086be8d7e0ff420606ce01b017a835b840407e91ada0002c4d043d3f7243c898510f0260c4c0097f130c1c4a360c6880d821bd835f862901b017a820200000873087a54b087910f0,
0x108d23288190009e051809f803c006f096a37a422d04591a0a114c2200da003f433306cd88321c4633786658de31bbe0db8182080406cc0cc81938e22116413bc26b84be0f0c37a80cc0168026804a42a1054317c01fa070107ee100c1fc040487fa10300ce46ce0bd41adc1fa46b68000b13410f4fdc930d1c4c37b80328060,
0x11b90389869e8bd41adc1fa46b68000b13410f4fdc90f221e2a26871402e81c4637506f600e91bf0077440d07fc09b437106e30dc502de38947100d730fd038086be8c521c4c34f45ea0d6e0fd235b4000589a087a43b0fdc90f2261443c07138a95041c009401383fc07f6100400009a90e40093421b00651be409d00580da8,
0x121e443c47150e1705cc294470d0d7d1afc31480d8080802e613683fe081a03ba2f503f48d6d0fd03808000589a087a54b08791d8a3b2c4c3c87110ee880eacdcece0e291c2e05a45288e1a09ae0ba01b30d7e0ff4206062901b0101037086dc80b2017203300668dd401e035f40b984da0ff820680ee849701f41fa07010e18,
0x12a5843c88782ab421c50f14ece0e2c1c48388c6bb87e91ada35b87150000b13410f4fdc90f250b2a46544d8e2b02901324666034a056c388c7148e2806de136c3fe081a03ba125c6ea00cc08ec02c870c0dc81b72370807d00f0019a030c05c87e81c0435f43fa080f036020207130d3d17a835b83f48d6d0001626821e9fb9,
0x10f0c28b40c8818802b6051809981281c4e38a82a107e81c0420446be8d7e0fdc20183f808090fe8203c3fc0815100220a86ce0c5203602f506b708080fd235b4000589a087a43b0fdc90f21c5c02942300ddc0000a0e542ca919508e087c7168dbe05920ad07038e241afa35f87040df4058a120c7078c5205660000439843d,
0x11b201fa07010000b1347ee2350c5e14cf838c068e8df31b00000021e90f31c5e288c3900d9d049a10d8032827e1be43604057006908cc114c6d00d9b1c5a03b46f18de21ba837001b7030406360ba071108b21c5830dc7158476096438246fa01f71b3006e4417880b10060e201ae034a06640c9c3f984ec09d0134426484be,
0x10001626821e9fb83b3aa46542cc6a18bc238cc24602dd01ca35bc6cc80b305d0364c6ed02aa1c5e000152a843d3b3aa46542ca67d54ef20f4a9510e2507038c86cd8d9d1bb8000148ca8594cfa3b1941c8e311c2204a00b401620f0c135c19303640e86274419d87ee100c1fe840c07e91ada0cc01a40da5065e0d181a28344,
0x11c6c369419d833a06880d141a300003f547ee2350a67c8c4238d46f80e0508aa24b804a0d9b1c6236747000d4d1afa1fa46b68000b134767548ca859507299f471a0df008aa381404a0d9b1c6236747000e321b30259c40587f3039c13086a6833c1c600d206d2832f1b201fa07010811102835f46bf07e91ada0d101a28346,
0x10fd235b4000589a087a7ee0ecea91950b3188471c0e321b3006b00e7080b066238d06a687f31b4a38d4261033a1c2238d809a0133097c38cc1a30345068836403f40e021010204440a0d7e0fe020243f48d6d1c5e0002c4d043d3f70767548ca8598d4238dc6d28db51b9837e41a20345068c0000fd510f23f70767635092ff,
0x10fe020243fb08120ff420606df8482059805040a10143028805140a304c90fe8203c3f48d6d0fd038081a48e37067838e07170e2f0001626821e90ec3b3aa46542c9fb725fc38e471901ce1b3038d06a681bd10160cec1a487f31b4a130819c03371b20203840888141afc0d1c6c881451b7e05082648e370fe8203c3f40e02,
0x11c74384c19002f5017002d405984b50930364c0fd01dd03e00aa86d988eb1bc837841ee03040ffc374825004e112000de854a8069004a08580138da007f610082008d9b000020c840d092c0fa21d0840207fc06c80d4819304ef09b4135c2668786066036480cc017102d0055009484be1b1234f82a10be0105235f83f70806,
0x1523238f871d8df91bd638f071d0d91028c05140a104c9068e38dc6c807e81c041fd040787e91ada36fc7170e2f0001626821e90ec3b3aa46542c8e3d1b4a210041f80003f547ee0fda1fb23f6c4c3471e0da51b9a372c0001faa3f707674fda1fb23f6c438c97f8e3b1b9837e471c8e2f0001626821e90ec3b3aa46542c9fb7,
0x1087a43b0ece9fb750b038fc24c02f503ba32f040d024e0ff80cc026d04be1c7821080b88d3e1bd605140a101411c240ce451684c20fe6202c6cc0e01086a36546cd80c30184030070204761a1006c069e8bd4056c06b871e8da21b201fa07010808102235f43f808090fe8203c3f48d6d1b7e38b87178000b13410f48761d9d,
0x1026804a470e833c1c2428b426107f306220bec16e880b095412742460d981c02043407e00e21b2a030c66f04761a100ad82a10be00fd038084088d7d0fdc20183f808090fe8203c3fb08121b7e38b87178d3d036020200e7081403c420740f80bd41052034006880d201a6035424182cb18a406fc71f080e0fd235b4000589a,
0x1059631480df8e3e101c1fa46b68e3f0001626821e90ec3b3a7edc9868e401b64025404500890110118022a844b1b36385418204a012002a54190030905ea009410b0027096a129824c03fb080410040fd01ec03ba0000419082610341f443a18742100820003fe035206600c9827784e409b4133425f0786033006040b88154,
0x108040fec3a10ccc06780c8017a84c219bc12d424c07f305d00b740fd01dd0000202c6ea048c106420683e88d9801d2038840207fc06a40cc01930e0f09de136826684be0f0c36480cc017d02e2055009a01290a842f803f40e02102235f43f708060fe020243fb08121c5c38bc0e7081403e02f5041480d001a2034806a8483,
0x10906314816581bf1c7c36403f40e02101c1fa46b68e2e1c5e0002c4d043d21d876747218e12145a13083f9880b1b3038047078e411c3c1fa070108111afa1fc040487f4101e36fc69e8bd4037e20383f48d6d000162688791fb85230df749860e421c303720000130e25fc4c308788e410608128070a0900152a0858012801f,
0x10fd235b47178000b13410f48760e461c1a2a507208b691be2369c6cd8df91b4638006658992035c07306cf81a5037e074c6cf0805101020384088814102e1fa46b68000b13443c8876130e3b384c30a968e4503b6206867c87fc17a813686f5084102e21fa070107e91ada0002c4d043d3b384c347220e401c7821084208e42,
0x11b9c02c81530d93016e39186bf07e91ada0002c4d043d3b38392040581b90fe6381c5168aee1c4a0b246ca048310ac31485ea07f0101238bc06a0dd11b8e372806180c11c880aa01730d8c054e0a986c980b71afc37386dd8dc11ba803b87230d7d0fd235b4000589a087a7670a960e4710ac36505ea0e451c88390c6df8e2e,
0x10596120c6290e4901a80ba07240dd401dc35f46e38dca1c8c1fa070107f010121fa46b68000b13410f542c8e4a02e237ac26d01460ff8132440d0dbf1c6e076c6b701ae037e33e43f40e02101020383fa080f0fd235b46e50e461c900002c4d043d2a5a392470701ae039806940df81d31c8e2014404080e1022205040b8e2f,
0x11b94371c08380ee01a802dc7230d900fd038086be8d7e0fe020243f48d6d0001626821e8e4b152a08581070025003e10081fe03fb000026a470803491b4638d071b85420a862f801550d93016e35f866f0d9b1c08368848003301b4a0cbc1bc84e11b220cb46c804be1a7c05f027007fe104007a05ea049f020e37406df8e23,
0x11be636006cd00ed01d211ac2468da11c9635f86be87e91ada0002c4d0e4c1b54090c11f0c881bce32f802d0db1190e32240450089011032f4127024a086a39281980da5065e0cb425f02511a7c36446ed837902f8366c6df84e109c038107118da20ffc0b2c410048303d031485ea0e4919bc0ba01550e48093e37506c98dd0,
0x159a07ee043a92fe0cb239642100e4d0000990872c04171c9a000137f0e5708243934000267e1cac101072680004df839541ff0e4d000099f072a05661c980000a958e530ac439300001fb71ca415847260000261e39442af0e4c0000766c728055d1c9800008798e4f0ab839300001b7f1c9c15047260000000c39346df8a20,
0x10868376c6d002f51b3632f07020cde1b441fcc6db8472056c11e06da0e4e0000767421da91950b07ee144d8e5b1bfe2d286fa8dfc1c2c393c7290e511cac000021daab43f7054b043a90f00cae39686d2018c06f205f00bd836b02e205bc09d033909d4138427004db09b413042610d900ff820703ff0822100420b87290000,
0x1079c1fe840c87e9131035f424702e81cb61fcc6db8472056c11e06da0e511c9e394c0001d9d0876a46542c1fb81cba04e472c84c10000b340fdc08750cb2397009c8e5909821fa072d00fa092c374c3f48d7e08d80aa86f382431bc036a812a8c88088432f8039005a1bde321c644808d01140224044024a00cc094465e8435,
0x11b5828806d10e511c9e395872f80003b3a10ed48c9fb91cc21fe840c84d303a60d9865681db1036395c00029193f7221d432ba8592a5a39807018de51bcc39380000ed51cbe20280d707f01c2c12f057603320fd2288072b00003b3a10ed42c1fb90cae397869f016702c837e425d84d21b9237d43f40e5c0fe020280d80db3,
0x110e639943f98e5c101a0000fdc065910ea39901e70819091c074c1740cad03b638586d98e6210361fa46bf84781b6839747308e571cac0000ece843b5232195c73180d31bfa11f86ff8b4a1bea37f03f48d7f1ca2393c72900000876aad0fdc06572a5e39886fe8e0f01a637e87048dfe1bf237d46fe0e161cc039783f407e9,
0x10fe820400e0847f05960d2873087fc10381fa473284781b6839440001d9d087654bc97f1fb91cce132470f034a02e2398426d0e640fe81fa04080dfa0382383c7030df91b2e03c007700ed1c0212343fe081c0fd2399423c0db41ca2393c0001d9d087654bd55b8e66183e38040d80bac1afa20207278e4e1cac000021daab4,
0x10000767421d8e6b0fd806fc0dd0810077811fc16581b31018076040d81e410421fa473284781b6836cc7348e530000767421da9181cd41fa026904c102c404e47338e680ff420640ea8e660fe620343f48e6508f036d00001d9d087654bc73487e81cc439903f48e65000010ed55a152f3f7039a070f0171099213683f404c5,
0x119780b304108827105a20c006602f5093037e470780fa092e374c063047a1c16368473587e81cc839447290e4f1cac395472700003b3a21d4fdc29191cda0f3840c8dcf03a60fa41f083e707ba38586d98822105020b84188e0b1ba6395872a800010eadf7032ba89a566a54b873607e81cc8398c7308e6a0fd2399423c0db4,
0x11ce0385870f89f11ba63958728800010ea4bf9bee1fb95230195c7378b4a1c2c120c70f82cb1cda1fa07320df91c1e03e824b8dd3018c11e87058da11cd6394872b0e511c9e0000ece88753f7039b86c50da502d0059c0b3036306c40d841b004d209a61fe840c8df71bec07546f40dcf1ba437f00fb81ec03e807a07360482,
0x10fe620343fe081c0ffc2088401082e1bf2393c72c0e51000021d487110ee21c843c0fdcc622880c196473887ec037e07040dd08100fe813246f581710274136826087e81cde120c165834a036620303f9880d03b0206c3fe081c03c820846fc8e0f01f4125c6e980c608f4382c6d08e6b1cdc394c7288e4f0000767443aa918,
0x11c9c393c72b00003b3a438948ca89a1ce6075440c8dcf0ff407dc0f601f403d0134c73607e81ce20ba01b3048219780b307380e6e1c1e03e807a02f50198031824b849808f4374c7058830105a209c4108da11cd6395872a8e4e1c9e0000ece88751ce436586ea0dd113de36240c6017c02f605c40b7813a09d4138026d04c1,
0x1056c0b2c6660cbc1b4239ac0d8080803822eb040707e91ce4393c72a8e4e1cac0000ecea91a21c4a26c73a881a03ba1ff024c04db05ea0dbc6d08e6b17581fa06bf87e91ce4395872700003b3a7ee548d8e7408aa366c04a0d9d1b460aa86c982fb1b3437b40768dd41a100ba06d08e6b1afa35f80d8080817581fa47390e54,
0x13b3aa26d48c291a1cf004d070f04be09920cc81a50ccc19780ba06ea00e91cec39d06be87f010121fd040787e81afe34f45d607e91ce4394472a8e4e1cac0000ece9fb91cee387826481680694135c73983661cea1fd040787fa10301fa06bf8d3d17581fa47390e741ca2395872700003b3a7ee48710e760186383c23b0483,
0x1068a0d102648e1e06d605c426d84da0ff820680ee849805ea39e06d08e6b0fe8203c69e8bac1b201fa06bf87e91ce439dc7290e511cac39380001d9d5136a46073c80951b5e1154044808806220bec16e844b095412742460d9b021a03f00710d051cea368473581ce1028078840e81f010522eb03f48e7219bc393872b0000,
0x11ce436847358e4f1c9c39580001d9d1cf603f06cc849d1b260bec15500c0017a115c6f384760502090c15b0c9f1ade09606440448088432f804a808000e401686438c891944022c0450089011032f46cd8e041b4439e466f0da11cd635f80d8080803c420745d607e91ce4393c7270e541cbe39580001d9d513639e86d28346,
0x1016c394073d8e4f1cac000021e90e221d639fc53882d21b66361c5360dbc1ca039ec000043d875476588778e7e1c1811ec23b02bb0564000021eb71c3b2e39f46c10d8b1b52127c0838d8e1b2a11d006180c21c9e394073d8000087a438887210ea6e3a39f016584831ce6383c07800e91ba80ba073d01c1175835f440707e9,
0x11cf6393c000043d21c4aadc8721d961d060be473f0d871b78394073d8000087a76588778e820182361873e0e7f1ca039ec7278000087a438955b9d9621e043b88720e810fd02d287320db313ea0f383fd081919681fa44c40e0a1afa394872a8e501cf6394c000289a087a3b1955b0e801b0c39f405c80b8016e02cc6e180c0,
0x11afa39f40608e841cf839fc7288e551ca6000144d043d21c8438874381bf1c4820383f48dd3092e035807a00d01ca0393c73d8000523010f48728e861b5a36b86ec8dd81baa37587420e80010e01bc034844d1b40397c73d8000513410f487102211d0a39f47418e7c1cfe000021e90e2556e43907420e1b1d0238207410e50,
0x16fb854bc7460e681b6627d41e707fa1032262070587e91d1439547298000513410ed55b0e8b01d238642468bac1afa393c7270e56000010ec4398e8a1d103a18000289a523010f47448dec17581fa4705847a018c3a1c72b0e4e1cf6000144d043d21c83a203f40dfb1cc836cc4fa83ce0ff403e840c84970fd23a084c40e0a,
0x1507c54b874709c0037e202840803a8077836cc7460e0f1c0c03c00770c1f1bf212347008e8b1c161fa47450da11d12393c72b00005134a4607468d88099206300be017102de04e83fa04ea09c0136826088100fd00d280e089f11cd0382c6e987f3101a1ff040e07fe1044200841707e91d14394472b0000523010ec97f2b34,
0x11cf6397c000289a21c443c021e8e900fd038706fd8e8e08aa11446cd8da0012802386f78db01bb237606ea8dd61b2c126c3fe07f31b700be0076881c101a377860f848d0fd211f87458e8a1b4430dc7468e0f1ca2397c73d8e4f1ca0000144d10e221e043b021d8e8f13800784405081f07500f646d98e56000021d553a2a5a,
0x11c9e3a5400012ff1d2c36d873d8e940000438c74a8cde1d2600007638e94091a3a2c6d08e88016603a40590e911d24000144d0e931c3636e46de8e501cf600008788e9201dc12347478e8b1b423a40000289a21c443c07488cf91c4811443f4808e1ba636c024b8d9b1bb237606ea8dd601e83a147440da2186e3a347280e4f,
0x101da3778246881b0ff820703f48e8a1cac3a5c7288e961cf6397c74a0e4f1d243a5472800000876aadc74c8e8e1d181154702047e0fd23a2860f849b05f002546d80dd81baa37646eb8dd61b2c36e06ef00ee091a3a5c74b0e931cf63a547490e4f1ca03a5072f80000876aadc10f8e981c1e3a487278e950000df7474b8df9,
0x11d1832f074d0e9903c807600d98821103620303f4847e1d14394c74b8e961d263938000043b1d3632606fd0dfc1c2c1fa026d836f1b28076c1ea881b0ff820703f48e8a1cf63a5074b8e511d2c3958000043b52363a6870b0dfa0fd0136c1b78d9403b60f542290d9b1d30023c6d80dd91bb037546eb0dd71b2c36e06cb80ee,
0x101e8033024b847a1ba6382c41688211d243a5474e8e4f1d38000043a8ea01b0a047008484b109440fa41ef88251062033023d0e0b018239f007a04971ba63a4874a8e9d1c9e3a70000087543ae3a7c6cd0e4f1d2a3a7400036fd1d3c39fc74a8e9c000043ac74e8da11d36000021e0e9c0fd806fc0e7881010320ef01e70db3,
0x103823a8c753000056683aa86c98e9e1d4a00021d20ea91d083a5474e0ea40000439075401b01d4c3a880002a741d4e2eb072b0e4e1d420000a970ea61afc3a840002a541d4a35f47508000556c3a904070ea10000f05075188081d420001daa0ea20fd23a8000008721d42361408b0106095a127c0fa01e81b663a7c0608e7c,
0x46c20ea71d4a3a7074a8e7b1ca03aac7550eac00003ab41538ea9000076647560dba1d500000ec68eab]

def cP : List Nat := cP_0 ++ cP_1 ++ cP_2

theorem unsat : ¬ FormulaSat (Lk.enc2 (4 + 4) 5 g Rp.rows44) :=
  checkW_sound _ cK 15 cP (by decide +kernel)

theorem lower : ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4475 : ℕ).testBit (4 * u.val + v.val)) 5 :=
  Rp.rep_lower44 _ 5 g hg unsat

theorem upper : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4475 : ℕ).testBit (4 * u.val + v.val)) 6 := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 12] }], output := 13 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.Monotone2]

end Cert

end PEqualNP.Outside.L_meta_5562

theorem PEqualNP.Outside.L_meta_5562 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4475 : ℕ).testBit (4 * u.val + v.val)) 6 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4475 : ℕ).testBit (4 * u.val + v.val)) 5 :=
  ⟨PEqualNP.Outside.L_meta_5562.upper, PEqualNP.Outside.L_meta_5562.lower⟩
