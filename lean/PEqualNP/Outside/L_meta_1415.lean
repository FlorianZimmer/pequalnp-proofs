import Mathlib
import PEqualNP.Defs
-- The live-wire checker is adapted from ljste's PR 2918 and jfsantoropereira's L-meta-1007.
-- The checker is reused from Vkuparin, L-meta-1419. Apache-2.0.
-- Samples and monotone circuit witnesses are generated for the ten tables here.
namespace PEqualNP.Outside.L_meta_1415_aux

abbrev B := BitVec 256
abbrev Sig := B × B
def top : B := BitVec.allOnes 256
def zero : Sig := (0,0)
def one : Sig := (top,top)
def target : Sig := (top,0)
def neg (a : Sig) : Sig := (~~~a.1,~~~a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1,a.2 ||| b.2) else (a.1 &&& b.1,a.2 &&& b.2)
def sep (d : Bool) (a : Sig) : B :=
  if d then a.1 ^^^ a.2 else a.1 &&& ~~~a.2
def unionSep (d : Bool) : List Sig → B
  | [] => 0
  | a::l => sep d a ||| unionSep d l

def dropped (del v : List Sig) : List Sig := v.filter (fun x => !(del.contains x))

abbrev Cov := B × B × B

def addCov (z : B) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Sig) : Cov :=
  v.foldr (fun a c => addCov (sep d a) c) (0,0,0)

def takeOne (c : Cov) (a : B) : B := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : B) : B :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : B) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : B) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : B) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Sig} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (sep d a)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

private theorem cov_union (d : Bool) (v : List Sig) : (coverage d v).1=unionSep d v := by
  induction v with
  | nil => rfl
  | cons a v ih => change sep d a ||| (coverage d v).1 = (sep d a ||| unionSep d v); rw [ih]

private lemma bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]



-- Each bit position pairs a positive and a negative input row.
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one

-- A set records the distinct signals needed by the remaining gates.
-- Read backwards, a gate replaces its output with the operand or operands.
def Live : Nat → Nat → Finset Sig → Prop
  | 0, t, S => t = 0 ∧ S = {target}
  | k+1, t, S =>
    (∃ u U a, t = u+1 ∧ S = insert a U ∧ proper a ∧ neg a ∉ insert a U ∧ Live k u (insert (neg a) U)) ∨
    (∃ U a b d, S = insert a (insert b U) ∧ proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live k t (insert (bin d a b) U))

lemma Live.stop : Live 0 0 {target} := ⟨rfl,rfl⟩

lemma Live.unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k+1) (t+1) (insert a U) := Or.inl ⟨_,_,_,rfl,rfl,ha,hfresh,tail⟩

lemma Live.binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k+1) t (insert a (insert b U)) := Or.inr ⟨_,_,_,_,rfl,ha,hb,hab,hfresh,tail⟩

lemma liveInd {P : ∀ k t S, Live k t S → Prop}
    (stop : P 0 0 {target} Live.stop)
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)), P k t (insert (neg a) U) tail → P (k+1) (t+1) (insert a U) (Live.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)), P k t (insert (bin d a b) U) tail → P (k+1) t (insert a (insert b U)) (Live.binary ha hb hab hfresh tail))
    {k t S} (h : Live k t S) : P k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl⟩ := h
    exact stop
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail (ih tail)
    · exact binary ha hb hab hf tail (ih tail)

lemma liveCases {P : ∀ k t S, Live k t S → Prop}
    (stop : P 0 0 {target} Live.stop)
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)), P (k+1) (t+1) (insert a U) (Live.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)), P (k+1) t (insert a (insert b U)) (Live.binary ha hb hab hfresh tail))
    {k t S} (h : Live k t S) : P k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl⟩ := h
    exact stop
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail
    · exact binary ha hb hab hf tail

private lemma target_proper : proper target := by unfold proper target zero one top; decide
private lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h using liveInd with
  | stop => simpa using target_proper
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using liveInd with
  | stop => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩

private lemma sep_unary (t : Nat) (a : Sig) (i : Nat)
    (h : (sep (decide (0<t)) (neg a)).getLsbD i = true) :
    (sep true a).getLsbD i = true := by
  by_cases hi : i < 256
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 256 ≤ i)] at h

private lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 256
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 256 ≤ i)] at h

private lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 256)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h

private lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 256) :
    ∃ a ∈ S, (sep (decide (0<t)) a).getLsbD i = true := by
  induction h using liveInd with
  | stop =>
    refine ⟨target,by simp,?_⟩
    change (BitVec.allOnes 256 &&& ~~~(0 : B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 256)] <;> simp [hi]
  | unary ha hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    simp only [Finset.mem_insert] at hx
    simp only [Nat.zero_lt_succ,decide_true]
    rcases hx with rfl | hU
    · exact ⟨_,Finset.mem_insert_self _ _,sep_unary _ _ _ h⟩
    · exact ⟨x,Finset.mem_insert_of_mem hU,sep_weaken _ _ _ hi h⟩
  | binary ha hb hab hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl | hU
    · rcases sep_binary _ _ _ _ _ h with h | h
      · exact ⟨_,Finset.mem_insert_self _ _,h⟩
      · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),h⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),h⟩
private lemma mem_unionSep (d : Bool) (v : List Sig) (i : Nat) :
    (unionSep d v).getLsbD i = true ↔ ∃ a ∈ v, (sep d a).getLsbD i = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a v ih => simp only [unionSep,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp] <;> aesop

private lemma live_cover {k t S} {v : List Sig} (h : Live k t S) (he : v.toFinset=S) :
    unionSep (decide (0<t)) v = top := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨a,hm,ha⟩ := live_sep h i hi
  have hmem : a ∈ v := List.mem_toFinset.mp (he.symm ▸ hm)
  simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using (mem_unionSep _ _ _).2 ⟨a,hmem,ha⟩

private lemma union_append (d : Bool) (l r : List Sig) :
    unionSep d (l++r) = unionSep d l ||| unionSep d r := by
  induction l with
  | nil => simp [unionSep]
  | cons a l ih => simp [unionSep,ih,BitVec.or_assoc]

def keepOf (U : Finset Sig) (del : List Sig) : List Sig := del.filter (fun a => decide (a ∈ U))

private lemma edit_list {v del : List Sig} {U : Finset Sig}
    (hv : v.Nodup) (hd : del.Nodup) (he : v.toFinset = del.toFinset ∪ U) :
    (keepOf U del ++ dropped del v).Nodup ∧ (keepOf U del ++ dropped del v).toFinset = U := by
  have memv (x : Sig) : x ∈ v ↔ x ∈ del ∨ x ∈ U := by
    change x ∈ v ↔ _
    rw [← List.mem_toFinset,he]
    simp
  constructor
  · rw [List.nodup_append]
    refine ⟨hd.filter _,hv.filter _,?_⟩
    intro a ha b hb eq
    subst b
    simp [keepOf] at ha
    simp [dropped] at hb
    exact hb.2 ha.1
  · ext x
    simp only [List.mem_toFinset,List.mem_append,List.mem_filter,keepOf,dropped,decide_eq_true_eq,
      Bool.not_eq_true',List.contains_eq_mem,memv]
    by_cases h : x ∈ del <;> simp_all

private lemma recover_perm (del v : List Sig) (hv : v.Nodup) (hd : del.Nodup)
    (hs : ∀ x ∈ del, x ∈ v) : v.Perm (del ++ dropped del v) := by
  apply List.perm_of_nodup_nodup_toFinset_eq hv
  · rw [List.nodup_append]
    refine ⟨hd,hv.filter _,?_⟩
    intro a ha b hb e
    subst b
    simp [dropped] at hb
    exact hb.2 ha
  · ext x
    simp only [List.mem_toFinset,List.mem_append,dropped,List.mem_filter,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not]
    by_cases h : x ∈ del <;> simp_all

private lemma one_rest (d : Bool) {v : List Sig} {a : Sig} (hv : v.Nodup) (ha : a ∈ v) :
    v.length-1=(dropped [a] v).length ∧
      takeOne (coverage d v) (sep d a)=unionSep d (dropped [a] v) := by
  have p := recover_perm [a] v hv (by simp) (by simpa using ha)
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d p]
    exact (cov_one _ _).trans (cov_union _ _)

private lemma two_rest (d : Bool) {v : List Sig} {a b : Sig} (hv : v.Nodup)
    (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    v.length-2=(dropped [a,b] v).length ∧
      takeTwo (coverage d v) (sep d a) (sep d b)=unionSep d (dropped [a,b] v) := by
  have p := recover_perm [a,b] v hv (by simp [hab]) (by simp [ha,hb])
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d p]
    exact (cov_two _ _ _).trans (cov_union _ _)

open PEqualNP.CircuitLowerBounds

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  obtain ⟨p,n⟩ := a
  simp only [bin,one,zero,top,reduceCtorEq,ite_true,ite_false,BitVec.and_allOnes,BitVec.or_allOnes,BitVec.and_zero,BitVec.or_zero,BitVec.and_self,BitVec.or_self,Prod.mk.injEq,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one,top]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def isNot (op : GateOp) : Bool := match op with | .not => true | _ => false

lemma isNot_iff (op : GateOp) : isNot op = true ↔ op = .not := by cases op <;> simp [isNot]

def witness (allow : Bool) (w : List Sig) (z : Sig) : Prop :=
  (allow = true ∧ ∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness false w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness (isNot g.op) w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness true w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨rfl,a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,isNot,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness false w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,isNot,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness false w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,isNot,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,isNot,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {flag : Bool} {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ witness flag w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ t' ≤ t+flag.toNat ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨flagOn,a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,by simp [flagOn],Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,by omega,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ t ≤ gs.countP (fun g => isNot g.op) ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,by simp,Live.stop,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,hcount,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hcnt,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    refine ⟨l,u,T,by simp; omega,?_,hu,hT⟩
    cases hf : isNot g.op <;> simp [List.countP_cons,hf] at hcnt ⊢ <;> omega

def bit (side : Bool) (i : Fin 256) (a : Sig) : Bool :=
  (if side then a.1 else a.2).getLsbD i.val

private lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit,zero]
private lemma bit_one (s i) : bit s i one = true := by
  cases s <;> change (BitVec.allOnes 256).getLsbD i.val = true <;> rw [BitVec.getLsbD_allOnes] <;> simp
private lemma bit_neg (s i) (a : Sig) : bit s i (neg a) = !(bit s i a) := by
  cases s <;> simp only [bit,neg,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_not,i.isLt,decide_true,Bool.true_and]
private lemma bit_bin (s i d) (a b : Sig) : bit s i (bin d a b) =
    (if d then bit s i a || bit s i b else bit s i a && bit s i b) := by
  cases s <;> cases d <;> simp only [bit,bin,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]

private lemma b_read (s i) (w : List Sig) (j : Nat) :
    (w.map (bit s i)).getD j false = bit s i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _ _).symm
  | some a => rfl

private lemma run_bit (s i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit s i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit s i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _ _
    | cons a l ih =>
      change bit s i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _ _
    | cons a l ih =>
      change bit s i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit s i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _ _

private lemma execute_bits (gs : List Gate) (s i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit s i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit s i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit s i g w (hg g (by simp))]


def evalT (T : ℕ) (x : Fin 5 → Bool) := Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)
def sample (raw : List Sig) (s : Bool) (i : Fin 256) (j : Fin 5) := bit s i (raw.getD j.val zero)
private lemma sample_list (raw : List Sig) (raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw) (s i) : List.ofFn (sample raw s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 5 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (T : ℕ) (raw : List Sig) (raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw)
    (sample_ok : ∀ s i, evalT T (sample raw s i) = s) (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = evalT T x) : target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have project (s i) : bit s i (w.getD C.output zero) = s := by
    rw [←b_read]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ (fun g hg => (h g hg).1)]
    have eq := he (sample raw s i)
    rw [sample_list raw raw_id,sample_ok] at eq
    exact eq
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project true ⟨i,hi⟩
      change (w.getD C.output zero).1.getLsbD i = true at p
      change _ = (BitVec.allOnes _).getLsbD _
      simpa only [BitVec.getLsbD_allOnes,hi,decide_true] using p
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project false ⟨i,hi⟩
      change (w.getD C.output zero).2.getLsbD i = false at p
      have hz : (0 : B).getLsbD i=false := by simp
      exact p.trans hz.symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)

private lemma necessary (raw : List Sig) (every_input : raw.all (fun a => unionSep true (raw.erase a) != top) = true) {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ raw) : raw.toFinset=S := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_,hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp every_input a hr
  have cov : unionSep true (raw.erase a) = top := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨b,hb,h⟩ := live_sep l i hi
    have ba : b ≠ a := fun he => hn (he ▸ hb)
    have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
    have eq := (mem_unionSep true _ _).mpr ⟨b,hm,sep_weaken _ _ _ hi h⟩
    simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using eq
  simp [cov] at fail

def special : List Sig := []
def gateAvailable (v : List Sig) (g : Sig) : Bool :=
  !(v.contains g) && g != zero && g != one

def tryGate (k t : Nat) (r : List Sig → Bool) (v rest : List Sig) (n : Nat) (c : B) (g : Sig)
    (keep : List (List Sig)) : Bool :=
  let d := decide (0<t)
  let base := sep d g ||| c
  if n = k-t then
    base == top && gateAvailable v g && r (g::rest)
  else keep.any (fun h => decide (n+h.length+1 ≤ k-t+1) &&
    (base ||| unionSep d h == top) && gateAvailable v g && r (g::(h++rest)))

def unaryAt (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a : Sig) : Bool :=
  !(special.contains a) &&
    tryGate k t r v (dropped [a] v) (v.length-1) (takeOne c (sep (decide (0<t)) a)) (neg a) [[],[a]]

def unaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  let c := coverage (decide (0<t)) v
  v.any (unaryAt k t r v c)

def allowedKeeps (a b : Sig) : List (List Sig) :=
  [[],[a],[b],[a,b]].filter (fun w => w.all fun x => !(special.contains x))

def fastBinary (r : List Sig → Bool) (v : List Sig) (a b : Sig) (ua ub : B) : Bool :=
  let rest := dropped [a,b] v
  let use := fun (g : Sig) => gateAvailable v g && r (g::rest)
  ((ua &&& ~~~b.1) == 0 && (ub &&& ~~~a.1) == 0 &&
    !(special.contains a) && !(special.contains b) && use (bin false a b)) ||
    ((ua &&& b.2) == 0 && (ub &&& a.2) == 0 && use (bin true a b))

def slowBinary (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a b : Sig) : Bool :=
  let rest := dropped [a,b] v
  let mask := takeTwo c (sep (decide (0<t)) a) (sep (decide (0<t)) b)
  ((!(special.contains a) && !(special.contains b)) &&
    tryGate k t r v rest (v.length-2) mask (bin false a b) [[],[a],[b],[a,b]]) ||
    tryGate k t r v rest (v.length-2) mask (bin true a b) (allowedKeeps a b)

def scanPairs {α : Type} (p : α → α → Bool) : List α → Bool
  | [] => false
  | a :: t => t.any (p a) || scanPairs p t

lemma scanPairs_complete {α : Type} (p : α → α → Bool) {a b : α} {v : List α}
    (ha : a ∈ v) (hb : b ∈ v) (hne : a ≠ b)
    (hab : p a b = true) (hba : p b a = true) : scanPairs p v = true := by
  induction v with
  | nil => simp at ha
  | cons h v ih =>
    simp only [scanPairs, Bool.or_eq_true]
    by_cases eqA : a = h
    · subst h
      exact Or.inl (List.any_eq_true.mpr ⟨b, (List.mem_cons.mp hb).resolve_left (Ne.symm hne), hab⟩)
    · have ha' := (List.mem_cons.mp ha).resolve_left eqA
      by_cases eqB : b = h
      · subst h
        exact Or.inl (List.any_eq_true.mpr ⟨a, ha', hba⟩)
      · exact Or.inr (ih ha' ((List.mem_cons.mp hb).resolve_left eqB))

def binaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  let d := decide (0<t)
  let c := coverage d v
  if t == 0 && v.length == k+2 then
    let acts := v.map (fun a => (a, c.2.1 &&& sep false a))
    scanPairs (fun a b => fastBinary r v a.1 b.1 a.2 b.2) acts
  else scanPairs (slowBinary k t r v c) v

def stepTest (k t : Nat) (v : List Sig) (u b : List Sig → Bool) : Bool :=
  if t>k+1 ∨ v.length>k+1-t+1 then false else
    v == [target] || (decide (0<t) && unaryMoves k (t-1) u v) || binaryMoves k t b v

def search : Nat → Nat → List Sig → Bool
  | 0, _, v => v == [target]
  | k+1,t,v => stepTest k t v (search k (t-1)) (search k t)

private lemma gate_found {k t m : Nat} {v rest h : List Sig} {g : Sig} {opts : List (List Sig)}
    {S : Finset Sig} {r : List Sig → Bool} (l : Live m t S)
    (hle : m ≤ k) (hp : proper g) (ha : g ∉ v) (hh : h ∈ opts)
    (hn : (g::(h++rest)).Nodup) (he : (g::(h++rest)).toFinset=S)
    (hr : r (g::(h++rest)) = true) : tryGate k t r v rest rest.length (unionSep (decide (0<t)) rest) g opts = true := by
  obtain ⟨ht,hc⟩ := live_size l
  rw [←he,List.toFinset_card_of_nodup hn] at hc
  simp only [List.length_cons,List.length_append] at hc
  have hl : rest.length+h.length+1 ≤ k-t+1 := by omega
  have cv := live_cover l he
  rw [unionSep,union_append] at cv
  have cov : (sep (decide (0<t)) g ||| unionSep (decide (0<t)) rest) ||| unionSep (decide (0<t)) h = top := by
    rw [← cv]; ac_rfl
  by_cases tight : rest.length=k-t
  · have hz : h.length=0 := by omega
    have hem : h=[] := List.length_eq_zero_iff.mp hz
    subst h
    have ok : sep (decide (0<t)) g ||| unionSep (decide (0<t)) rest = top := by
      simpa [unionSep] using cov
    simp [tryGate,tight,ok,gateAvailable,ha,hp.1,hp.2,hr] at *
  · have hav : gateAvailable v g = true := by simp [gateAvailable, ha, hp.1, hp.2]
    simp only [tryGate, ite_eq_right tight, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq, hav, and_true]
    exact ⟨h,hh,⟨hl,cov⟩,hr⟩

private lemma unique_needed (c : Cov) (a b : Sig) (op : Bool)
    (h : sep false (bin op a b) ||| takeTwo c (sep false a) (sep false b)=top) :
    ((c.2.1 &&& sep false a) &&& (if op then b.2 else ~~~b.1)) |||
    ((c.2.1 &&& sep false b) &&& (if op then a.2 else ~~~a.1))=0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hh := congrArg (fun z : B => z.getLsbD i) h
  clear h
  cases op <;> simp only [sep,bin,ite_false,ite_true,takeTwo,top,BitVec.getLsbD_allOnes,
    BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,BitVec.getLsbD_zero,
    reduceCtorEq,hi,decide_true,Bool.true_and] at hh ⊢ <;>
    cases ax : a.1.getLsbD i <;> cases ay : a.2.getLsbD i <;>
    cases bx : b.1.getLsbD i <;> cases byy : b.2.getLsbD i <;>
    cases um : c.2.1.getLsbD i <;> simp [ax,ay,bx,byy,um] at hh ⊢

private lemma fast_ok {k r v c a b}
    (hlen : v.length-2=k) (h : slowBinary k 0 r v c a b = true) :
    fastBinary r v a b (c.2.1 &&& sep false a) (c.2.1 &&& sep false b) = true := by
  simp only [slowBinary,tryGate,Nat.sub_zero,hlen,ite_true,decide_false,Bool.or_eq_true,
    Bool.and_eq_true,beq_iff_eq] at h
  simp only [fastBinary, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  rcases h with ⟨⟨ha,hb⟩,⟨hc,hav⟩,hr⟩ | ⟨⟨hc,hav⟩,hr⟩
  · obtain ⟨h1,h2⟩ := BitVec.or_eq_zero_iff.mp (unique_needed c a b false hc)
    exact Or.inl ⟨⟨⟨⟨h1,h2⟩,ha⟩,hb⟩,hav,hr⟩
  · obtain ⟨h1,h2⟩ := BitVec.or_eq_zero_iff.mp (unique_needed c a b true hc)
    exact Or.inr ⟨⟨h1,h2⟩,hav,hr⟩

private lemma unary_found {m t k : Nat} {U : Finset Sig} {a : Sig} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a U) (hle : m ≤ k)
    (fresh : neg a ∉ insert a U) (ha : a ∉ special) (l : Live m t (insert (neg a) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (neg a) U → r v = true) :
    unaryMoves k t r v = true := by
  let h := keepOf U [a]
  let rest := dropped [a] v
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  obtain ⟨hn,eq⟩ := edit_list (del := [a]) (U := U) hv (by simp) (by simpa using he)
  change (h++rest).Nodup at hn
  change (h++rest).toFinset=U at eq
  have nn : neg a ∉ v := fun hm => fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : neg a ∉ U := fun hm => fresh (Finset.mem_insert_of_mem hm)
  have hnd : (neg a::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (neg a::(h++rest)).toFinset=insert (neg a) U := by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a]] := by by_cases hm : a ∈ U <;> simp [h,keepOf,hm]
  apply List.any_eq_true.mpr
  refine ⟨a,ah,?_⟩
  unfold unaryAt
  obtain ⟨hlen,hmask⟩ := one_rest (decide (0<t)) hv ah
  rw [hlen,hmask]
  apply Bool.and_eq_true_iff.mpr
  exact ⟨by simp [ha], gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩

private lemma slow_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (hra : a ∈ special → d = true ∧ a ∉ U)
    (hrb : b ∈ special → d = true ∧ b ∉ U)
    (l : Live m t (insert (bin d a b) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (bin d a b) U → r v = true) :
    slowBinary k t r v (coverage (decide (0<t)) v) a b = true := by
  let g := bin d a b
  let h := keepOf U [a,b]
  let rest := dropped [a,b] v
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  obtain ⟨hn,eq⟩ := edit_list (del := [a,b]) (U := U) hv (by simp [hab]) (by simpa using he)
  change (h++rest).Nodup at hn
  change (h++rest).toFinset=U at eq
  have nn : g ∉ v := fun hm => fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : g ∉ U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  have hnd : (g::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (g::(h++rest)).toFinset=insert g U := by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a],[b],[a,b]] := by
    by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;> simp [h,keepOf,ha,hb]
  have allow : h ∈ allowedKeeps a b := by
    apply List.mem_filter.mpr
    refine ⟨opts,List.all_eq_true.mpr (fun x hx => ?_)⟩
    have hm : x ∈ U := (List.mem_filter.mp hx).2 |> of_decide_eq_true
    rcases List.mem_cons.mp (List.mem_filter.mp hx).1 with rfl | hx
    · simpa using fun ha : x ∈ special => (hra ha).2 hm
    · obtain rfl := List.mem_singleton.mp hx
      simpa using fun hb : x ∈ special => (hrb hb).2 hm
  obtain ⟨hlen,hmask⟩ := two_rest (decide (0<t)) hv ah bh hab
  unfold slowBinary
  dsimp only
  rw [hlen,hmask]
  cases d with
  | false =>
    have na : a ∉ special := fun ha => Bool.false_ne_true (hra ha).1
    have nb : b ∉ special := fun hb => Bool.false_ne_true (hrb hb).1
    apply Bool.or_eq_true_iff.mpr
    left
    exact Bool.and_eq_true_iff.mpr ⟨by simp [na,nb],
      gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩
  | true =>
    apply Bool.or_eq_true_iff.mpr
    right
    exact gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn allow hnd e (ih _ hnd e)

private lemma binary_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (hra : a ∈ special → d = true ∧ a ∉ U)
    (hrb : b ∈ special → d = true ∧ b ∉ U)
    (l : Live m t (insert (bin d a b) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (bin d a b) U → r v = true) :
    binaryMoves k t r v = true := by
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have h1 := slow_found hv he hle hab fresh hra hrb l ih
  have e' : v.toFinset = insert b (insert a U) := by rwa [Finset.insert_comm b a]
  have hf : bin d b a ∉ insert b (insert a U) := by rwa [bin_comm d b a, Finset.insert_comm b a]
  have ht : Live m t (insert (bin d b a) U) := by rwa [bin_comm d b a]
  have h2 := slow_found hv e' hle hab.symm hf hrb hra ht (by simpa only [bin_comm d b a] using ih)
  unfold binaryMoves
  split
  · rename_i cut
    simp only [Bool.and_eq_true, beq_iff_eq] at cut
    obtain ⟨rfl,hvlen⟩ := cut
    have hlen : v.length - 2 = k := by omega
    let f := fun x => (x, (coverage false v).2.1 &&& sep false x)
    have na : f a ∈ v.map f := List.mem_map_of_mem ah
    have nb : f b ∈ v.map f := List.mem_map_of_mem bh
    exact scanPairs_complete _ na nb (fun e => hab (congrArg Prod.fst e))
      (fast_ok hlen h1) (fast_ok hlen h2)
  · exact scanPairs_complete _ ah bh hab h1 h2

private lemma reduced_step {m t S : Nat} {s : Finset Sig} {v : List Sig} {u b : List Sig → Bool}
    (h : Live m t s) (hb : m ≤ S+1) (hv : v.Nodup) (he : v.toFinset = s)
    (hu : ∀ w, w.Nodup → ∀ l ≤ S, Live l (t-1) w.toFinset → u w = true)
    (hb' : ∀ w, w.Nodup → ∀ l ≤ S, Live l t w.toFinset → b w = true) :
    stepTest S t v u b = true := by
  have size := live_size h
  rw [← he, List.toFinset_card_of_nodup hv] at size
  rw [stepTest, if_neg (by omega)]
  induction h using liveCases with
  | stop =>
    have p : v.Perm [target] := List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [he])
    have eq := List.perm_singleton.mp p
    simp [eq]
  | @unary m t U a ha hf tail =>
    apply Bool.or_eq_true_iff.mpr
    left
    apply Bool.or_eq_true_iff.mpr
    right
    apply Bool.and_eq_true_iff.mpr
    refine ⟨by simp, unary_found hv he (by omega) hf (by simp [special]) tail ?_⟩
    intro w hn hs
    exact hu w hn m (by omega) (hs.symm ▸ tail)
  | @binary m t U a b d ha hc hab hf tail =>
    apply Bool.or_eq_true_iff.mpr
    right
    apply binary_found hv he (by omega) hab hf (by simp [special]) (by simp [special]) tail
    intro w hn hs
    exact hb' w hn m (by omega) (hs.symm ▸ tail)

lemma search_complete {m t : Nat} {S : Finset Sig} (h : Live m t S) (k : Nat) (hk : m ≤ k)
    (v : List Sig) (hv : v.Nodup) (hs : v.toFinset = S) : search k t v = true := by
  induction k generalizing m t S v with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    obtain ⟨rfl,rfl⟩ := h
    have p : v.Perm [target] := List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [hs])
    simp [search, List.perm_singleton.mp p]
  | succ k ih =>
    rw [search]
    apply reduced_step h hk hv hs <;>
      exact fun w hn l hl hh => ih hh hl w hn rfl


lemma notCount (gs : List Gate)
    (single : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j) :
    gs.countP (fun g => isNot g.op) ≤ 1 := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have rest : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j := by
      intro i j hi hj
      exact Fin.succ_inj.mp (single i.succ j.succ hi hj)
    by_cases hg : g.op = .not
    · have z : gs.countP (fun h => isNot h.op) = 0 := by
        apply List.countP_eq_zero.mpr
        intro a ha
        obtain ⟨i,hi⟩ := List.mem_iff_get.mp ha
        intro h
        have hiNot : (gs.get i).op = .not := by rw [hi]; exact (isNot_iff _).mp h
        have eqn := single (0 : Fin (g::gs).length) i.succ hg hiNot
        exact Fin.succ_ne_zero i eqn.symm
      have hf : isNot g.op = true := (isNot_iff _).mpr hg
      simp [List.countP_cons,hf,z]
    · have flag : isNot g.op = false := Bool.eq_false_iff.mpr (fun h => hg ((isNot_iff _).mp h))
      simpa [List.countP_cons,flag] using ih rest

theorem cost (T : ℕ) (raw : List Sig) (s : ℕ)
    (raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw)
    (samples : ∀ b i, evalT T (sample raw b i) = b)
    (nd : raw.Nodup) (len : raw.length = 5)
    (essential : raw.all (fun a => unionSep true (raw.erase a) != top) = true)
    (test : ∀ t : Fin 2, search s t.val raw = false)
    (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (single : ∀ i j : Fin C.gates.length, (C.gates.get i).op = .not → (C.gates.get j).op = .not → i = j)
    (correct : ∀ x, C.eval (List.ofFn x) = evalT T x) : s < C.gates.length := by
  by_contra! small
  obtain ⟨k,t,S,hk,count,live,sub⟩ := extract C.gates raw legal (circuit_target T raw raw_id samples C legal correct)
  have oneNot := notCount C.gates single
  have eq := necessary raw essential live sub
  have size := live_size live
  rw [←eq,List.toFinset_card_of_nodup nd,len] at size
  have good := search_complete live s (by omega) raw nd eq
  exact Bool.false_ne_true ((test ⟨t,by omega⟩).symm.trans good)


open PEqualNP.CircuitLowerBounds

def raw0 : List Sig := [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0xaa55555554aaaaaaa955555552aaaaaaa55555554aaaaaaa955555552aaaaaaa),
  (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0xcc999999993333333266666664ccccccc999999993333333266666664ccccccc),
  (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0xf0e1e1e1e1c3c3c3c3878787870f0f0f0e1e1e1e1c3c3c3c3878787870f0f0f0),
  (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0xfe01fe01fc03fc03f807f807f00ff00fe01fe01fc03fc03f807f807f00ff00),
  (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0xfffe0001fffc0003fff80007fff0000fffe0001fffc0003fff80007fff0000)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut0Zero : search 3 0 raw0 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut0One : search 3 1 raw0 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma table0 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ a b : Fin gs.length, (gs.get a).op = .not → (gs.get b).op = .not → a = b)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 2147483648 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 2147483648 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have bound := cost 2147483648 raw0 3 rfl (by decide +kernel) (by decide +kernel)
    rfl (by decide +kernel) (by
      intro t
      fin_cases t
      · exact ruledOut0Zero
      · exact ruledOut0One) ⟨gs,o⟩ legal hn he
  exact ⟨[⟨.and, [3, 4]⟩, ⟨.and, [2, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [0, 7]⟩], 8, by simp, by exact Nat.succ_le_of_lt bound, by decide +kernel⟩

def raw1 : List Sig := [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0x952aaa54a95552a54aaa952a5554a952aaa54a95552a54aaa952a5554a952aaa),
  (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0x264ccc99326664c99333264c99993264ccc99326664c99333264c99993264ccc),
  (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0x3870f0e1c387870e1c3c3870e1e1c3870f0e1c387870e1c3c3870e1e1c3870f0),
  (0xffffff00000007fffffffffffffe0000000ffffffffffffffc0000001fffffff, 0xc07f00fe03f807f01fc03f80fe01fc07f00fe03f807f01fc03f80fe01fc07f00),
  (0xfffffffffffff80000003ffffffffffffff00000007fffffffffffffe0000000, 0xff8000fffc0007ffe0003fff0001fff8000fffc0007ffe0003fff0001fff8000)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut1Zero : search 3 0 raw1 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut1One : search 3 1 raw1 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma table1 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ a b : Fin gs.length, (gs.get a).op = .not → (gs.get b).op = .not → a = b)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 2155905024 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 2155905024 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have bound := cost 2155905024 raw1 3 rfl (by decide +kernel) (by decide +kernel)
    rfl (by decide +kernel) (by
      intro t
      fin_cases t
      · exact ruledOut1Zero
      · exact ruledOut1One) ⟨gs,o⟩ legal hn he
  exact ⟨[⟨.or, [3, 4]⟩, ⟨.and, [2, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [0, 7]⟩], 8, by simp, by exact Nat.succ_le_of_lt bound, by decide +kernel⟩

def raw2 : List Sig := [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0xa4952aaa4952aaa4952aaa4952aaa4952aaa4952aaa4952aaa4952aaa4952aaa),
  (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0xc9264ccc9264ccc9264ccc9264ccc9264ccc9264ccc9264ccc9264ccc9264ccc),
  (0xfffffffffffffff0000000fffffffffffffffffffff0000000ffffffffffffff, 0xe3870f0e3870f0e3870f0e3870f0e3870f0e3870f0e3870f0e3870f0e3870f0),
  (0xfffffffffffffffffffff0000000fffffffffffffffffffff0000000fffffff, 0xfc07f00fc07f00fc07f00fc07f00fc07f00fc07f00fc07f00fc07f00fc07f00),
  (0xf0000000fffffffffffffffffffff0000000fffffffffffffffffffff0000000, 0xfff8000fff8000fff8000fff8000fff8000fff8000fff8000fff8000fff8000)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut2Zero : search 5 0 raw2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut2One : search 5 1 raw2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma table2 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ a b : Fin gs.length, (gs.get a).op = .not → (gs.get b).op = .not → a = b)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 2290122752 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 2290122752 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have bound := cost 2290122752 raw2 5 rfl (by decide +kernel) (by decide +kernel)
    rfl (by decide +kernel) (by
      intro t
      fin_cases t
      · exact ruledOut2Zero
      · exact ruledOut2One) ⟨gs,o⟩ legal hn he
  exact ⟨[⟨.or, [2, 3]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [5, 7]⟩, ⟨.and, [1, 8]⟩, ⟨.and, [0, 9]⟩], 10, by simp, by exact Nat.succ_le_of_lt bound, by decide +kernel⟩

def raw3 : List Sig := [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0xa9524a952a4952a5492a54a9254a9524a952a4952a5492a54a9254a9524a952a),
  (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0x326493264c9264c9924c9932499326493264c9264c9924c9932499326493264c),
  (0xfff8000000fffffffffffffffffffffffffff0000001ffffffffffffffffffff, 0xc3871c3870e3870e1c70e1c38e1c3871c3870e3870e1c70e1c38e1c3871c3870),
  (0xffffffffff0000001ffffffc0000007ffffffffffffe0000003ffffff8000000, 0xfc07e03f80fc07f01f80fe03f01fc07e03f80fc07f01f80fe03f01fc07e03f80),
  (0xffffffffffffffffe00000000000007fffffffffffffffffffc0000000000000, 0x7ffc000fff8001fff0003ffe0007ffc000fff8001fff0003ffe0007ffc000)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut3Zero : search 3 0 raw3 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut3One : search 3 1 raw3 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma table3 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ a b : Fin gs.length, (gs.get a).op = .not → (gs.get b).op = .not → a = b)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 2290122880 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 2290122880 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have bound := cost 2290122880 raw3 3 rfl (by decide +kernel) (by decide +kernel)
    rfl (by decide +kernel) (by
      intro t
      fin_cases t
      · exact ruledOut3Zero
      · exact ruledOut3One) ⟨gs,o⟩ legal hn he
  exact ⟨[⟨.and, [3, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [0, 7]⟩], 8, by simp, by exact Nat.succ_le_of_lt bound, by decide +kernel⟩

def raw4 : List Sig := [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0x5550952aaa12a5554254aaa84a95550952aaa12a5554254aaa84a95550952aaa),
  (0xfff8000000fffffffffffffffffffffffffff0000001ffffffffffffffffffff, 0x6665264ccca4c999949933329326665264ccca4c999949933329326665264ccc),
  (0xffffffffff0000001ffffffffffffffffffffffffffe0000003fffffffffffff, 0x87863870f0c70e1e18e1c3c31c387863870f0c70e1e18e1c3c31c387863870f0),
  (0xffffffffffffffffe0000003ffffffffffffffffffffffffffc0000007ffffff, 0xf807c07f00f80fe01f01fc03e03f807c07f00f80fe01f01fc03e03f807c07f00),
  (0xfffffffffffffffffffffffc0000007ffffffffffffffffffffffffff8000000, 0x7ff8000fff0001ffe0003ffc0007ff8000fff0001ffe0003ffc0007ff8000)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut4Zero : search 7 0 raw4 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut4One : search 7 1 raw4 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma table4 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ a b : Fin gs.length, (gs.get a).op = .not → (gs.get b).op = .not → a = b)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 2826993664 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 2826993664 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have bound := cost 2826993664 raw4 7 rfl (by decide +kernel) (by decide +kernel)
    rfl (by decide +kernel) (by
      intro t
      fin_cases t
      · exact ruledOut4Zero
      · exact ruledOut4One) ⟨gs,o⟩ legal hn he
  exact ⟨[⟨.or, [1, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [6, 9]⟩, ⟨.and, [5, 10]⟩, ⟨.and, [0, 11]⟩], 12, by simp, by exact Nat.succ_le_of_lt bound, by decide +kernel⟩

def raw5 : List Sig := [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0x2a54a84a952a12a54a84a952a12a54a84a952a12a54a84a952a12a54a84a952a),
  (0xfffffffffffffffffffffffffffffffc000000ffffffffffffffffffffffffff, 0x4c993293264ca4c993293264ca4c993293264ca4c993293264ca4c993293264c),
  (0x3ffffffffffffffffffffffffffffffff0000003fffffffffffffffffff, 0x70e1c31c3870c70e1c31c3870c70e1c31c3870c70e1c31c3870c70e1c31c3870),
  (0xfffffc000000ffffffc000000fffffffffffffffffffc000000ffffffc000000, 0x80fe03e03f80f80fe03e03f80f80fe03e03f80f80fe03e03f80f80fe03e03f80),
  (0xffffffffffff0000000000000ffffffffffffffffffffffffff0000000000000, 0xff0003ffc000fff0003ffc000fff0003ffc000fff0003ffc000fff0003ffc000)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut5Zero : search 5 0 raw5 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut5One : search 5 1 raw5 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma table5 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ a b : Fin gs.length, (gs.get a).op = .not → (gs.get b).op = .not → a = b)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 2826993792 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 2826993792 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have bound := cost 2826993792 raw5 5 rfl (by decide +kernel) (by decide +kernel)
    rfl (by decide +kernel) (by
      intro t
      fin_cases t
      · exact ruledOut5Zero
      · exact ruledOut5One) ⟨gs,o⟩ legal hn he
  exact ⟨[⟨.or, [1, 2]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [5, 8]⟩, ⟨.and, [0, 9]⟩], 10, by simp, by exact Nat.succ_le_of_lt bound, by decide +kernel⟩

end PEqualNP.Outside.L_meta_1415_aux

namespace PEqualNP.Outside.L_meta_1415.SignedWork
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Fn (X : Type) := X → Bool
def zeroF {X : Type} : Fn X := fun _ => false
def canonical {X : Type} (origin : X) (f : Fn X) : Fn X := fun x => xor (f x) (f origin)
def operation {X : Type} (v : Fin 4) (a b : Fn X) : Fn X :=
  fun x => if v = 0 then a x || b x else if v = 1 then a x && b x
    else if v = 2 then a x && !b x else b x && !a x

def kind (join a b : Bool) : Fin 4 :=
  if a == b then (if join != a then 0 else 1) else (if join == a then 2 else 3)

theorem canonical_binary {X : Type} (o : X) (a b : Fn X) (join : Bool) :
    canonical o (fun x => if join then a x || b x else a x && b x) =
    operation (kind join (a o) (b o)) (canonical o a) (canonical o b) := by
  funext x
  simp only [canonical,operation,kind]
  generalize a o = u, b o = v, a x = t, b x = z
  cases join <;> cases u <;> cases v <;> cases t <;> cases z <;> rfl

theorem canonical_compl {X : Type} (o : X) (a : Fn X) :
    canonical o (fun x => !a x) = canonical o a := by
  funext x
  simp only [canonical]
  cases a x <;> cases a o <;> rfl

theorem canonical_const {X : Type} (o : X) (b : Bool) :
    canonical o (fun _ => b) = zeroF := by cases b <;> rfl

inductive Steps {X : Type} (initial : Set (Fn X)) : Nat → Set (Fn X) → Prop where
  | start : Steps initial 0 initial
  | append {n T} (prior : Steps initial n T) (v : Fin 4) {a b : Fn X}
      (ha : a ∈ T) (hb : b ∈ T) : Steps initial (n+1) (insert (operation v a b) T)

def binary (g : Gate) : Bool := match g.op with
  | .and | .or => g.inputs.length == 2
  | _ => false

private def applyG {X : Type} (g : Gate) (w : List (Fn X)) : Fn X :=
  fun x => g.op.eval (g.inputs.map fun j => (w.getD j zeroF) x)

private def step {X : Type} (w : List (Fn X)) (g : Gate) : List (Fn X) := w ++ [applyG g w]

private theorem mem_getD {X : Type} (w : List (Fn X)) (T : Set (Fn X)) (o : X)
    (hz : zeroF ∈ T) (hw : ∀ f ∈ w, canonical o f ∈ T) (j : Nat) :
    canonical o (w.getD j zeroF) ∈ T := by
  by_cases hj : j < w.length
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using hw w[j] (List.getElem_mem ..)
  · have h : w[j]? = none := List.getElem?_eq_none (by omega)
    rw [List.getD_eq_getElem?_getD, h]
    exact hz

private theorem advance {X : Type} (o : X) {S T : Set (Fn X)} {k : Nat}
    (hs : Steps S k T) (hz : zeroF ∈ T) (g : Gate) (w : List (Fn X))
    (hw : ∀ f ∈ w, canonical o f ∈ T)
    (legal : g.op = .and ∨ g.op = .or ∨ g.op = .not) (arity : g.inputs.length ≤ 2) :
    ∃ k' T', Steps S k' T' ∧ k' ≤ k + (if binary g then 1 else 0) ∧
      T ⊆ T' ∧ canonical o (applyG g w) ∈ T' := by
  rcases g with ⟨op,ins⟩
  cases ins with
  | nil =>
    refine ⟨k,T,hs,by simp [binary],Set.Subset.rfl,?_⟩
    rcases legal with rfl|rfl|rfl <;> exact hz
  | cons i rest =>
    have hi := mem_getD w T o hz hw i
    cases rest with
    | nil =>
      refine ⟨k,T,hs,by simp [binary],Set.Subset.rfl,?_⟩
      rcases legal with rfl|rfl|rfl
      · rw [show applyG ⟨.and,[i]⟩ w = w.getD i zeroF by funext x; simp [applyG,GateOp.eval]]
        exact hi
      · rw [show applyG ⟨.or,[i]⟩ w = w.getD i zeroF by funext x; simp [applyG,GateOp.eval]]
        exact hi
      · change canonical o (fun x => !(w.getD i zeroF x)) ∈ T
        rwa [canonical_compl]
    | cons j more =>
      cases more with
      | cons => simp at arity
      | nil =>
        have hj := mem_getD w T o hz hw j
        rcases legal with rfl|rfl|rfl
        · let v := kind false ((w.getD i zeroF) o) ((w.getD j zeroF) o)
          refine ⟨k+1,_,hs.append v hi hj,by simp [binary],Set.subset_insert ..,?_⟩
          rw [show applyG ⟨.and,[i,j]⟩ w = (fun x => w.getD i zeroF x && w.getD j zeroF x) by
            funext x; simp [applyG,GateOp.eval]]
          exact Set.mem_insert_iff.mpr (Or.inl (canonical_binary o (w.getD i zeroF) (w.getD j zeroF) false))
        · let v := kind true ((w.getD i zeroF) o) ((w.getD j zeroF) o)
          refine ⟨k+1,_,hs.append v hi hj,by simp [binary],Set.subset_insert ..,?_⟩
          rw [show applyG ⟨.or,[i,j]⟩ w = (fun x => w.getD i zeroF x || w.getD j zeroF x) by
            funext x; simp [applyG,GateOp.eval]]
          exact Set.mem_insert_iff.mpr (Or.inl (canonical_binary o (w.getD i zeroF) (w.getD j zeroF) true))
        · exact ⟨k,T,hs,by simp [binary],Set.Subset.rfl,by change canonical o (fun x => !w.getD i zeroF x) ∈ T; rwa [canonical_compl]⟩

private theorem advance_list {X : Type} (o : X) (gs : List Gate) {S T : Set (Fn X)} {k : Nat}
    (hs : Steps S k T) (hz : zeroF ∈ T) (w : List (Fn X))
    (hw : ∀ f ∈ w, canonical o f ∈ T)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    ∃ k' T', Steps S k' T' ∧ k' ≤ k + (gs.filter binary).length ∧
      zeroF ∈ T' ∧ ∀ f ∈ gs.foldl step w, canonical o f ∈ T' := by
  induction gs generalizing T k w with
  | nil => exact ⟨k,T,hs,by simp,hz,hw⟩
  | cons g gs ih =>
    obtain ⟨hg,hl⟩ := legal g (by simp)
    obtain ⟨j,U,hj,bs,hU,mem⟩ := advance o hs hz g w hw hg hl
    have ww : ∀ f ∈ step w g, canonical o f ∈ U := by
      intro f hf
      rcases List.mem_append.mp hf with a|b
      · exact hU (hw f a)
      · simp only [List.mem_singleton] at b
        subst f
        exact mem
    obtain ⟨j',U',hr,hcost,hz',hws⟩ :=
      ih hj (hU hz) (step w g) ww (fun a h => legal a (by simp [h]))
    refine ⟨j',U',hr,?_,hz',hws⟩
    cases h : binary g <;> simp [h] at * <;> omega

private theorem getD_eval {X : Type} (w : List (Fn X)) (j : Nat) (x : X) :
    (w.map (fun f => f x)).getD j false = w.getD j zeroF x := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? <;> rfl

private theorem eval_fold {X : Type} (gs : List Gate) (w : List (Fn X)) (x : X) :
    (gs.foldl step w).map (fun f => f x) =
    gs.foldl (fun t g => t ++ [g.op.eval (g.inputs.map fun i => t.getD i false)])
      (w.map fun f => f x) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons,ih,step,applyG,List.map_append,List.map_cons,List.map_nil,getD_eval]

def sources (n : Nat) : Set (Fn (Fin n → Bool)) :=
  insert zeroF (Set.range (fun i : Fin n => fun x : Fin n → Bool => x i))

theorem circuit_to_signed (n : Nat) (C : Circuit) (basis : FanInTwo C) :
    ∃ k T, Steps (sources n) k T ∧ k ≤ (C.gates.filter binary).length ∧
      canonical (fun _ => false) (fun x => C.eval (List.ofFn x)) ∈ T := by
  let w : List (Fn (Fin n → Bool)) := List.ofFn fun i x => x i
  let o : Fin n → Bool := fun _ => false
  have hx : ∀ f ∈ w, canonical o f ∈ sources n := by
    intro f hf
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf
    apply Set.mem_insert_of_mem
    exact ⟨i, by funext x; simp [canonical,o]⟩
  have legal (g) (h : g ∈ C.gates) := basis g h
  have ok (g) (h : g ∈ C.gates) :
      (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
    simpa [Set.mem_insert_iff] using legal g h
  obtain ⟨k,T,hs,hk,hz,hw⟩ :=
    advance_list o C.gates (Steps.start : Steps (sources n) 0 _) (Set.mem_insert ..) w hx ok
  refine ⟨k,T,hs,by simpa using hk,?_⟩
  have eq : (fun x => C.eval (List.ofFn x)) = (C.gates.foldl step w).getD C.output zeroF := by
    funext x
    rw [← getD_eval]
    simp only [eval_fold,Circuit.eval,Circuit.wires]
    congr 2
    simp [w,List.map_ofFn,Function.comp_def]
  rw [eq]
  exact mem_getD _ _ o hz hw _

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false

theorem binary_plus_not (gs : List Gate) :
    (gs.filter binary).length + (gs.filter isNot).length ≤ gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have exclusive : binary g = false ∨ isNot g = false := by
      rcases g with ⟨op,l⟩
      cases op <;> simp [binary,isNot]
    cases hb : binary g <;> cases hn : isNot g <;> simp_all <;> omega

theorem signed_budget {n : Nat} (C : Circuit) (basis : FanInTwo C)
    (f : (Fin n → Bool) → Bool) (fzero : f (fun _ => false) = false)
    (evaluates : ∀ x, C.eval (List.ofFn x) = f x) :
    ∃ k T, Steps (sources n) k T ∧ f ∈ T ∧
      k + (C.gates.filter isNot).length ≤ C.size := by
  obtain ⟨k,T,path,hk,out⟩ := circuit_to_signed n C basis
  have eq : canonical (fun _ : Fin n => false) (fun x => C.eval (List.ofFn x)) = f := by
    funext x
    change xor (C.eval (List.ofFn x)) (C.eval (List.ofFn (fun _ : Fin n => false))) = _
    rw [evaluates, evaluates, fzero]
    cases f x <;> rfl
  rw [eq] at out
  refine ⟨k,T,path,out,?_⟩
  exact (Nat.add_le_add_right hk _).trans (binary_plus_not C.gates)

end PEqualNP.Outside.L_meta_1415.SignedWork

namespace PEqualNP.Outside.L_meta_1415.SignedWork

def project {X Y : Type} (φ : Y → X) (o : Y) (a : Fn X) : Fn Y :=
  canonical o (fun y => a (φ y))

theorem project_operation {X Y : Type} (φ : Y → X) (o : Y) (v : Fin 4) (a b : Fn X) :
    ∃ w, project φ o (operation v a b) = operation w (project φ o a) (project φ o b) ∨
         project φ o (operation v a b) = operation w (project φ o b) (project φ o a) := by
  let A : Fn Y := fun y => a (φ y)
  let B : Fn Y := fun y => b (φ y)
  fin_cases v
  · exact ⟨_,Or.inl (canonical_binary o A B true)⟩
  · exact ⟨_,Or.inl (canonical_binary o A B false)⟩
  · have h := canonical_binary o A (fun y => !B y) false
    rw [canonical_compl] at h
    exact ⟨_,Or.inl h⟩
  · have h := canonical_binary o B (fun y => !A y) false
    rw [canonical_compl] at h
    exact ⟨_,Or.inr h⟩

-- The third index counts gates whose restricted output is already available.
inductive RestrictedTrace {X Y : Type} (φ : Y → X) (o : Y) (S : Set (Fn X)) :
    Nat → Set (Fn X) → Nat → Prop where
  | start : RestrictedTrace φ o S 0 S 0
  | skip {k T lost} (prior : RestrictedTrace φ o S k T lost) (v : Fin 4) {a b : Fn X}
      (ha : a ∈ T) (hb : b ∈ T)
      (old : project φ o (operation v a b) ∈ project φ o '' T) :
      RestrictedTrace φ o S (k+1) (insert (operation v a b) T) (lost+1)
  | keep {k T lost} (prior : RestrictedTrace φ o S k T lost) (v : Fin 4) {a b : Fn X}
      (ha : a ∈ T) (hb : b ∈ T)
      (fresh : project φ o (operation v a b) ∉ project φ o '' T) :
      RestrictedTrace φ o S (k+1) (insert (operation v a b) T) lost

theorem trace_exists {X Y : Type} (φ : Y → X) (o : Y) {S T : Set (Fn X)} {k : Nat}
    (path : Steps S k T) : ∃ lost, RestrictedTrace φ o S k T lost := by
  induction path with
  | start => exact ⟨_,.start⟩
  | @append n T prior v a b ha hb ih =>
    obtain ⟨lost,h⟩ := ih
    by_cases old : project φ o (operation v a b) ∈ project φ o '' T
    · exact ⟨_,.skip h v ha hb old⟩
    · exact ⟨_,.keep h v ha hb old⟩

theorem restriction_saves {X Y : Type} {φ : Y → X} {o : Y} {S T : Set (Fn X)} {k lost : Nat}
    (h : RestrictedTrace φ o S k T lost) :
    ∃ n, Steps (project φ o '' S) n (project φ o '' T) ∧ n + lost = k := by
  induction h with
  | start => exact ⟨0,.start,rfl⟩
  | skip prior v ha hb old ih =>
    obtain ⟨n,path,eq⟩ := ih
    exact ⟨n,by simpa only [Set.image_insert_eq,Set.insert_eq_of_mem old] using path,by omega⟩
  | keep prior v ha hb fresh ih =>
    obtain ⟨n,path,eq⟩ := ih
    obtain ⟨w,h|h⟩ := project_operation φ o v _ _
    · refine ⟨n+1,?_,by omega⟩
      rw [Set.image_insert_eq,h]
      exact path.append w (Set.mem_image_of_mem _ ha) (Set.mem_image_of_mem _ hb)
    · refine ⟨n+1,?_,by omega⟩
      rw [Set.image_insert_eq,h]
      exact path.append w (Set.mem_image_of_mem _ hb) (Set.mem_image_of_mem _ ha)

end PEqualNP.Outside.L_meta_1415.SignedWork

namespace PEqualNP.Outside.L_meta_1415.RestrictionWork
open PEqualNP.Outside.L_meta_1415.SignedWork
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private theorem zero_operand {X : Type} (v : Fin 4) (a b : Fn X)
    (hz : a = zeroF ∨ b = zeroF) : operation v a b = a ∨ operation v a b = b := by
  rcases hz with rfl|rfl
  · fin_cases v
    · right; funext x; simp [operation,zeroF]
    · left; funext x; simp [operation,zeroF]
    · left; funext x; simp [operation,zeroF]
    · right; funext x; simp [operation,zeroF]
  · fin_cases v
    · left; funext x; simp [operation,zeroF]
    · right; funext x; simp [operation,zeroF]
    · left; funext x; simp [operation,zeroF]
    · right; funext x; simp [operation,zeroF]

private theorem unchanged {X Y : Type} {φ : Y → X} {o : Y} {S T : Set (Fn X)}
    {k lost : Nat} (h : RestrictedTrace φ o S k T lost) (p q : X)
    (base : ∀ f ∈ S, f p ≠ f q → project φ o f = zeroF) (hn : lost = 0) :
    ∀ f ∈ T, f p ≠ f q → f ∈ S ∧ project φ o f = zeroF := by
  induction h with
  | start => exact fun f hf hd => ⟨hf,base f hf hd⟩
  | skip => omega
  | @keep k T lost prior v a b ha hb fresh ih =>
    intro f hf hd
    rcases Set.mem_insert_iff.mp hf with rfl|mem
    · exfalso
      have diff : a p ≠ a q ∨ b p ≠ b q := by
        by_contra! both
        exact hd (by simp [operation,both.1,both.2])
      have z : project φ o a = zeroF ∨ project φ o b = zeroF := by
        rcases diff with da|db
        · exact .inl ((ih hn) a ha da).2
        · exact .inr ((ih hn) b hb db).2
      obtain ⟨w,e|e⟩ := project_operation φ o v a b
      · rcases zero_operand w _ _ z with eq|eq
        · exact fresh ⟨a,ha,(e.trans eq).symm⟩
        · exact fresh ⟨b,hb,(e.trans eq).symm⟩
      · rcases zero_operand w _ _ z.symm with eq|eq
        · exact fresh ⟨b,hb,(e.trans eq).symm⟩
        · exact fresh ⟨a,ha,(e.trans eq).symm⟩
    · exact ih hn _ mem hd

theorem essential_restriction {X Y : Type} (φ : Y → X) (o : Y) {S T : Set (Fn X)}
    {k : Nat} (path : Steps S k T) {f : Fn X} (out : f ∈ T)
    (p q : X) (separate : f p ≠ f q) (nonSource : f ∉ S)
    (base : ∀ s ∈ S, s p ≠ s q → project φ o s = zeroF) :
    ∃ n, Steps (project φ o '' S) n (project φ o '' T) ∧ n < k := by
  obtain ⟨lost,tr⟩ := trace_exists φ o path
  obtain ⟨n,short,len⟩ := restriction_saves tr
  have pos : lost ≠ 0 := fun h => nonSource ((unchanged tr p q base h f out separate).1)
  exact ⟨n,short,by omega⟩

end PEqualNP.Outside.L_meta_1415.RestrictionWork

namespace PEqualNP.Outside.L_meta_1415.LiveWork
open PEqualNP.Outside.L_meta_1415.SignedWork
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {dimension : Nat}
def row (r : (Fin (2^dimension))) (v : Fin dimension) : Bool := r.val.testBit v.val
def word (f : Fn (Fin dimension → Bool)) : (BitVec (2^dimension)) :=
  (BitVec.ofBoolListLE (List.ofFn fun r : (Fin (2^dimension)) => f (row r))).cast (by simp)
theorem bit_word (f : Fn (Fin dimension → Bool)) (r : (Fin (2^dimension))) : (word f).getLsbD r.val = f (row r) := by
  simp only [word,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left r.isLt,Option.getD_some]

def op (v : Fin 4) (a b : (BitVec (2^dimension))) : (BitVec (2^dimension)) :=
  if v = 0 then a ||| b else if v = 1 then a &&& b else if v = 2 then a &&& ~~~b else b &&& ~~~a

theorem pack_op (v : Fin 4) (a b : Fn (Fin dimension → Bool)) :
    word (operation v a b) = op v (word a) (word b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hx := bit_word (operation v a b) ⟨i,hi⟩
  have ha := bit_word a ⟨i,hi⟩
  have hb := bit_word b ⟨i,hi⟩
  fin_cases v <;> simpa [operation,op, -BitVec.getLsbD_eq_getElem, hi,ha,hb] using hx

inductive Live (goal : (BitVec (2^dimension))) : Nat → Finset (BitVec (2^dimension)) → Prop where
  | done : Live goal 0 {goal}
  | step {k N} (later : Live goal k N) (a b : (BitVec (2^dimension))) (v : Fin 4)
      (needed : op v a b ∈ N) (fresh : op v a b ∉ insert a (insert b (N.erase (op v a b)))) :
      Live goal (k+1) (insert a (insert b (N.erase (op v a b))))

theorem extract {S T : Set (Fn (Fin dimension → Bool))} {k d : Nat} {goal : (BitVec (2^dimension))}
    (h : Steps S k T) {N : Finset (BitVec (2^dimension))} (later : Live goal d N)
    (ready : ∀ w ∈ N, w ∈ word '' T) :
    ∃ budget A, Live goal budget A ∧ budget ≤ k+d ∧ ∀ w ∈ A, w ∈ word '' S := by
  induction h generalizing d N with
  | start => exact ⟨d,N,later,by omega,ready⟩
  | @append k T prior v f g hf hg ih =>
    let a := word f
    let b := word g
    let z := op v a b
    have seen (w) (hw : w ∈ N) (ne : w ≠ z) : w ∈ word '' T := by
      obtain ⟨u,hu,rfl⟩ := ready w hw
      rcases hu with rfl|mem
      · exact (ne (pack_op v f g)).elim
      · exact Set.mem_image_of_mem _ mem
    by_cases allReady : ∀ w ∈ N, w ∈ word '' T
    · obtain ⟨d',A,live,cost,sub⟩ := ih later allReady
      exact ⟨d',A,live,by omega,sub⟩
    · have need : z ∈ N := by
        by_contra no
        exact allReady (fun w hw => seen w hw (fun eq => no (eq ▸ hw)))
      have old : z ∉ word '' T := by
        intro previous
        apply allReady
        intro w hw
        by_cases e : w = z
        · simpa [e] using previous
        · exact seen w hw e
      have newReady : ∀ w ∈ insert a (insert b (N.erase z)), w ∈ word '' T := by
        simp only [Finset.mem_insert, Finset.mem_erase]
        rintro _ (rfl|rfl|⟨hne,hm⟩)
        · exact Set.mem_image_of_mem _ hf
        · exact Set.mem_image_of_mem _ hg
        · exact seen _ hm hne
      have fresh : z ∉ insert a (insert b (N.erase z)) := fun hz => old (newReady _ hz)
      obtain ⟨d',A,live,cost,sub⟩ := ih (later.step a b v need fresh) newReady
      exact ⟨d',A,live,by omega,sub⟩

theorem live_width {g k N} (h : Live (dimension := dimension) g k N) : N.card ≤ k+1 := by
  induction h with
  | done => simp
  | @step k N later a b v needed fresh ih =>
    have h1 := Finset.card_insert_le a (insert b (N.erase (op v a b)))
    have h2 := Finset.card_insert_le b (N.erase (op v a b))
    have h3 := Finset.card_erase_of_mem needed
    have h4 := Finset.card_pos.mpr ⟨_,needed⟩
    omega

def Separates (g : (BitVec (2^dimension))) (N : Finset (BitVec (2^dimension))) : Prop :=
  ∀ r s : (Fin (2^dimension)), (∀ w ∈ N, w.getLsbD r.val = w.getLsbD s.val) → g.getLsbD r.val = g.getLsbD s.val

theorem live_separates {g k N} (h : Live (dimension := dimension) g k N) : Separates g N := by
  induction h with
  | done => intro r s same; exact same _ (by simp)
  | @step k N later a b v needed fresh ih =>
    intro r s same
    apply ih r s
    intro w hw
    by_cases e : w = op v a b
    · subst w
      have ha := same a (by simp)
      have hb := same b (by simp)
      fin_cases v <;> simp [op, -BitVec.getLsbD_eq_getElem,r.isLt,s.isLt,ha,hb]
    · exact same w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨e,hw⟩)))

theorem live_nz {g k N} (h : Live (dimension := dimension) g k N) (ng : g ≠ 0) : (0 : (BitVec (2^dimension))) ∉ N := by
  induction h with
  | done => exact fun mem => ng (Finset.mem_singleton.mp mem).symm
  | @step k N later a b v needed fresh ih =>
    have az : a ≠ 0 := by
      rintro rfl
      fin_cases v <;> simp [op] at fresh
    have bz : b ≠ 0 := by
      rintro rfl
      fin_cases v <;> simp [op] at fresh
    intro mem
    rcases Finset.mem_insert.mp mem with e|m
    · exact az e.symm
    rcases Finset.mem_insert.mp m with e|m
    · exact bz e.symm
    exact ih (Finset.mem_of_mem_erase m)

def factors (g : (BitVec (2^dimension))) (L : List (BitVec (2^dimension))) (p : (BitVec (2^dimension))) : Bool :=
  if p &&& g == 0 || p &&& ~~~g == 0 then true else
    match L with
    | [] => false
    | a :: tail => factors g tail (p &&& a) && factors g tail (p &&& ~~~a)

theorem exists_bit (x : (BitVec (2^dimension))) (ne : x ≠ 0) : ∃ r : (Fin (2^dimension)), x.getLsbD r.val = true := by
  by_contra! absent
  apply ne
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simpa using absent (⟨i,hi⟩ : (Fin (2^dimension)))

theorem factors_of (g : (BitVec (2^dimension))) (L : List (BitVec (2^dimension))) (p : (BitVec (2^dimension)))
    (h : ∀ r s : (Fin (2^dimension)), p.getLsbD r.val = true → p.getLsbD s.val = true →
      (∀ w ∈ L, w.getLsbD r.val = w.getLsbD s.val) → g.getLsbD r.val = g.getLsbD s.val) :
    factors g L p = true := by
  induction L generalizing p with
  | nil =>
    rw [factors]
    split
    · rfl
    · rename_i fail
      simp only [Bool.or_eq_true,beq_iff_eq,not_or] at fail
      obtain ⟨r,hr⟩ := exists_bit _ fail.1
      obtain ⟨s,hs⟩ := exists_bit _ fail.2
      simp only [BitVec.getLsbD_and,Bool.and_eq_true,BitVec.getLsbD_not,s.isLt,
        decide_true,Bool.true_and,Bool.not_eq_true'] at hr hs
      have eq := h r s hr.1 hs.1 (by simp)
      simp_all
  | cons a L ih =>
    rw [factors]
    split
    · rfl
    · rw [Bool.and_eq_true]
      constructor
      · apply ih
        intro r s hr hs agree
        simp only [BitVec.getLsbD_and,Bool.and_eq_true] at hr hs
        apply h r s hr.1 hs.1
        intro w hw
        rcases List.mem_cons.mp hw with rfl|mem
        · exact hr.2.trans hs.2.symm
        · exact agree _ mem
      · apply ih
        intro r s hr hs agree
        simp only [BitVec.getLsbD_and,Bool.and_eq_true,BitVec.getLsbD_not,r.isLt,s.isLt,
           decide_true,Bool.true_and,Bool.not_eq_true'] at hr hs
        apply h r s hr.1 hs.1
        intro w hw
        rcases List.mem_cons.mp hw with rfl|mem
        · exact hr.2.trans hs.2.symm
        · exact agree _ mem

def codes : List (Fin 4) := [0,1,2,3]
def flags : List Bool := [false,true]
def keep (a b : (BitVec (2^dimension))) (u v : Bool) (w : (BitVec (2^dimension))) : Bool :=
  (w != a || u) && (w != b || v)
def next (L : List (BitVec (2^dimension))) (a b z : (BitVec (2^dimension))) (u v : Bool) : List (BitVec (2^dimension)) :=
  z :: L.filter (keep a b u v)

def find (g : (BitVec (2^dimension))) : Nat → List (BitVec (2^dimension)) → Bool
  | 0, L => g ∈ L
  | n+1, L => g ∈ L || (L.length ≤ n+2 && factors g L (~~~0) &&
      L.any (fun a => L.any (fun b => codes.any (fun v =>
        let z := op v a b
        z != 0 && z ∉ L && flags.any (fun u => flags.any (fun t =>
          let N := next L a b z u t
          N.length ≤ n+1 && find g n N))))))

theorem next_correct (L : List (BitVec (2^dimension))) (a b z : (BitVec (2^dimension))) (N : Finset (BitVec (2^dimension)))
    (h : L.toFinset = insert a (insert b (N.erase z))) (hz : z ∈ N) :
    (next L a b z (decide (a ∈ N)) (decide (b ∈ N))).toFinset = N := by
  ext w
  have mem : w ∈ L ↔ w = a ∨ w = b ∨ (w ≠ z ∧ w ∈ N) := by
    rw [← List.mem_toFinset, h]
    simp
  simp only [next,List.mem_toFinset,List.mem_cons,List.mem_filter,keep,Bool.and_eq_true,
    Bool.or_eq_true,bne_iff_ne,decide_eq_true_eq,mem]
  grind

theorem find_live {g k N} (h : Live (dimension := dimension) g k N) (ng : g ≠ 0) (n : Nat) (hk : k ≤ n)
    (L : List (BitVec (2^dimension))) (nd : L.Nodup) (eq : L.toFinset = N) : find g n L = true := by
  induction h generalizing n L with
  | done =>
    have mem : _ ∈ L := List.mem_toFinset.mp (eq.symm ▸ Finset.mem_singleton_self g)
    cases n <;> simp [find,mem]
  | @step k N later a b v needed fresh ih =>
    cases n with
    | zero => omega
    | succ n =>
      let z := op v a b
      let M := next L a b z (decide (a ∈ N)) (decide (b ∈ N))
      have rep : M.toFinset = N := next_correct L a b z N eq needed
      have znew : z ∉ L := fun he => fresh (eq ▸ List.mem_toFinset.mpr he)
      have noDup : M.Nodup := by
        apply List.nodup_cons.mpr
        exact ⟨fun mem => znew (List.mem_of_mem_filter mem),nd.filter _⟩
      have bound := live_width (later.step a b v needed fresh)
      rw [← eq, List.toFinset_card_of_nodup nd] at bound
      have width : L.length ≤ n+2 := by omega
      have bound2 := live_width later
      rw [← rep,List.toFinset_card_of_nodup noDup] at bound2
      have width2 : M.length ≤ n+1 := by omega
      have sep := live_separates (later.step a b v needed fresh)
      have fact : factors g L (~~~0) = true := by
        apply factors_of
        intro r s _ _ agree
        apply sep r s
        intro w hw
        exact agree w (List.mem_toFinset.mp (eq.symm ▸ hw))
      rw [find,Bool.or_eq_true]
      right
      simp only [Bool.and_eq_true,decide_eq_true_eq,List.any_eq_true,decide_not,bne_iff_ne] 
      refine ⟨⟨width,fact⟩,a, List.mem_toFinset.mp (eq.symm ▸ Finset.mem_insert_self ..),b,
        List.mem_toFinset.mp (eq.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..)), v,?_,?_,?_⟩
      · exact (by decide +kernel : ∀ t, t ∈ codes) v
      · exact ⟨(fun e => live_nz later ng (e ▸ needed)),by simpa using znew⟩
      · refine ⟨_,(by decide +kernel : ∀ t, t ∈ flags) _,_,(by decide +kernel : ∀ t, t ∈ flags) _,width2,?_⟩
        exact ih n (by omega) M noDup rep

-- A successor is already excluded if it cannot distinguish some pair of rows.
-- The other successors are proved separately and named in the supplied list.
def blocked (g : (BitVec (2^dimension))) (n : Nat) (L : List (BitVec (2^dimension))) (known : List (List (BitVec (2^dimension)))) : Bool :=
  g ∉ L && L.all (fun a => L.all (fun b => codes.all (fun v =>
    let z := op v a b
    z == 0 || z ∈ L || flags.all (fun u => flags.all (fun t =>
      let M := next L a b z u t
      M.length > n+1 || (g ∉ M && (!factors g M (~~~0) || M ∈ known)))))))

theorem blocked_sound {g : (BitVec (2^dimension))} {n : Nat} {L : List (BitVec (2^dimension))} {known : List (List (BitVec (2^dimension)))}
    (h : blocked g n L known = true) (used : ∀ M ∈ known, find g n M = false) :
    find g (n+1) L = false := by
  simp only [blocked,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at h
  apply Bool.eq_false_iff.mpr
  intro yes
  rw [find,Bool.or_eq_true] at yes
  rcases yes with had|pos
  · exact h.1 (of_decide_eq_true had)
  simp only [Bool.and_eq_true,List.any_eq_true,decide_eq_true_eq,bne_iff_ne] at pos
  obtain ⟨_,a,ha,b,hb,v,hv,⟨nz,fresh⟩,u,hu,t,ht,small,yes⟩ := pos
  have atGate := h.2 a ha b hb v hv
  simp only [Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq,nz,fresh,false_or,List.all_eq_true] at atGate
  have atNext := atGate u hu t ht
  let M := next L a b (op v a b) u t
  have invalid : ¬ M.length > n+1 := by change ¬ (next L a b (op v a b) u t).length > n+1; omega
  rcases atNext with overflow | atNext
  · exact invalid overflow
  change (decide (g ∉ M) && (!factors g M (~~~0) || decide (M ∈ known))) = true at atNext
  simp only [Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,
    Bool.not_eq_true'] at atNext
  change find g n M = true at yes
  rcases atNext.2 with excluded | mem
  · cases n with
    | zero => exact atNext.1 (of_decide_eq_true yes)
    | succ n =>
      simp only [find,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at yes
      rcases yes with mem | ⟨⟨_,pass⟩,_⟩
      · exact atNext.1 mem
      · exact Bool.noConfusion (excluded.symm.trans pass)
  · rw [used M mem] at yes
    contradiction

end PEqualNP.Outside.L_meta_1415.LiveWork

namespace PEqualNP.Outside.L_meta_1415.SmallThreshold
open PEqualNP.Outside.L_meta_1415.SignedWork PEqualNP.Outside.L_meta_1415.LiveWork
abbrev Input := Fin 4 → Bool
abbrev Word := BitVec 16
abbrev Row := Fin 16
def coord (i : Fin 4) : Word := ![43690,52428,61680,65280] i
def seed : List Word := [43690,52428,61680,65280]
private theorem coord_word : ∀ i : Fin 4, word (fun x => x i) = coord i := by decide +kernel

private theorem lower_of_nodes (f : Fn Input) (g : Word) (ng : g ≠ 0) (budget : Nat)
    (packed : word f = g) (left right : Fin 4 → Row)
    (relevant : ∀ i : Fin 4, g.getLsbD (left i).val ≠ g.getLsbD (right i).val ∧
      ∀ j : Fin 4, j ≠ i → (coord j).getLsbD (left i).val = (coord j).getLsbD (right i).val)
    (miss : find (dimension := 4) g budget seed = false)
    {k T} (path : Steps (sources 4) k T) (out : f ∈ T) : budget+1 ≤ k := by
  by_contra! small
  have has : ∀ w ∈ ({g} : Finset Word), w ∈ word '' T := by
    intro w hw
    rw [Finset.mem_singleton.mp hw,← packed]
    exact Set.mem_image_of_mem _ out
  obtain ⟨d,N,live,bound,sub⟩ := extract path (.done : Live (dimension := 4) g 0 {g}) has
  have nz : (0 : Word) ∉ N := live_nz live ng
  have eq : seed = List.ofFn coord := by decide +kernel
  have coord_of {w : Word} (hw : w ∈ N) : ∃ j, coord j = w := by
    obtain ⟨v,hv,he⟩ := sub w hw
    rcases hv with rfl | ⟨j,rfl⟩
    · have zero : word (zeroF : Fn Input) = 0 := by decide +kernel
      rw [zero] at he
      exact (nz (he ▸ hw)).elim
    · exact ⟨j,(coord_word j).symm.trans he⟩
  have start : seed.toFinset = N := by
    ext w
    rw [eq,List.mem_toFinset,List.mem_ofFn]
    constructor
    · rintro ⟨i,rfl⟩
      by_contra absent
      apply (relevant i).1
      apply live_separates live
      intro u hu
      obtain ⟨j,rfl⟩ := coord_of hu
      exact (relevant i).2 j (fun e => absent (e ▸ hu))
    · exact coord_of
  have hit := find_live live ng budget (by omega) seed (by decide +kernel) start
  exact Bool.noConfusion (miss.symm.trans hit)


def threshold (x : Input) : Bool :=
  decide (3 ≤ (List.ofFn x).count true)

def thresholdTwo (x : Input) : Bool :=
  decide (2 ≤ (List.ofFn x).count true)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_0 : find (dimension := 4) 59520 4 [10,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_1 : find (dimension := 4) 59520 4 [12,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_2 : find (dimension := 4) 59520 4 [34,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_3 : find (dimension := 4) 59520 4 [48,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_4 : find (dimension := 4) 59520 4 [68,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_5 : find (dimension := 4) 59520 4 [80,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_6 : find (dimension := 4) 59520 4 [136,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_7 : find (dimension := 4) 59520 4 [160,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_8 : find (dimension := 4) 59520 4 [170,204,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_9 : find (dimension := 4) 59520 4 [170,240,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_10 : find (dimension := 4) 59520 4 [170,21760,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_11 : find (dimension := 4) 59520 4 [170,21760,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_12 : find (dimension := 4) 59520 4 [170,43520,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_13 : find (dimension := 4) 59520 4 [170,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_14 : find (dimension := 4) 59520 4 [170,52224,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_15 : find (dimension := 4) 59520 4 [170,61440,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_16 : find (dimension := 4) 59520 4 [170,65450,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_17 : find (dimension := 4) 59520 4 [192,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_18 : find (dimension := 4) 59520 4 [204,170,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_19 : find (dimension := 4) 59520 4 [204,240,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_20 : find (dimension := 4) 59520 4 [204,13056,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_21 : find (dimension := 4) 59520 4 [204,13056,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_22 : find (dimension := 4) 59520 4 [204,43520,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_23 : find (dimension := 4) 59520 4 [204,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_24 : find (dimension := 4) 59520 4 [204,52224,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_25 : find (dimension := 4) 59520 4 [204,61440,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_26 : find (dimension := 4) 59520 4 [204,65484,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_27 : find (dimension := 4) 59520 4 [238,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_28 : find (dimension := 4) 59520 4 [238,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_29 : find (dimension := 4) 59520 4 [238,61166,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_30 : find (dimension := 4) 59520 4 [240,170,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_31 : find (dimension := 4) 59520 4 [240,204,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_32 : find (dimension := 4) 59520 4 [240,3840,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_33 : find (dimension := 4) 59520 4 [240,3840,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_34 : find (dimension := 4) 59520 4 [240,43520,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_35 : find (dimension := 4) 59520 4 [240,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_36 : find (dimension := 4) 59520 4 [240,52224,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_37 : find (dimension := 4) 59520 4 [240,61440,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_38 : find (dimension := 4) 59520 4 [240,65520,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_39 : find (dimension := 4) 59520 4 [250,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_40 : find (dimension := 4) 59520 4 [250,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_41 : find (dimension := 4) 59520 4 [250,64250,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_42 : find (dimension := 4) 59520 4 [252,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_43 : find (dimension := 4) 59520 4 [252,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_44 : find (dimension := 4) 59520 4 [252,64764,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_45 : find (dimension := 4) 59520 4 [514,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_46 : find (dimension := 4) 59520 4 [768,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_47 : find (dimension := 4) 59520 4 [1028,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_48 : find (dimension := 4) 59520 4 [1280,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_49 : find (dimension := 4) 59520 4 [2056,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_50 : find (dimension := 4) 59520 4 [2560,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_51 : find (dimension := 4) 59520 4 [2570,3084,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_52 : find (dimension := 4) 59520 4 [2570,3840,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_53 : find (dimension := 4) 59520 4 [2570,20560,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_54 : find (dimension := 4) 59520 4 [2570,20560,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_55 : find (dimension := 4) 59520 4 [2570,41120,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_56 : find (dimension := 4) 59520 4 [2570,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_57 : find (dimension := 4) 59520 4 [2570,49344,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_58 : find (dimension := 4) 59520 4 [2570,61440,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_59 : find (dimension := 4) 59520 4 [2570,64250,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_60 : find (dimension := 4) 59520 4 [2730,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_61 : find (dimension := 4) 59520 4 [3072,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_62 : find (dimension := 4) 59520 4 [3084,2570,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_63 : find (dimension := 4) 59520 4 [3084,3840,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_64 : find (dimension := 4) 59520 4 [3084,12336,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_65 : find (dimension := 4) 59520 4 [3084,12336,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_66 : find (dimension := 4) 59520 4 [3084,41120,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_67 : find (dimension := 4) 59520 4 [3084,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_68 : find (dimension := 4) 59520 4 [3084,49344,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_69 : find (dimension := 4) 59520 4 [3084,61440,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_70 : find (dimension := 4) 59520 4 [3084,64764,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_71 : find (dimension := 4) 59520 4 [3276,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_72 : find (dimension := 4) 59520 4 [3598,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_73 : find (dimension := 4) 59520 4 [3598,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_74 : find (dimension := 4) 59520 4 [3598,61166,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_75 : find (dimension := 4) 59520 4 [3840,240,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_76 : find (dimension := 4) 59520 4 [3840,240,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_77 : find (dimension := 4) 59520 4 [3840,2570,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_78 : find (dimension := 4) 59520 4 [3840,3084,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_79 : find (dimension := 4) 59520 4 [3840,41120,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_80 : find (dimension := 4) 59520 4 [3840,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_81 : find (dimension := 4) 59520 4 [3840,49344,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_82 : find (dimension := 4) 59520 4 [3840,61440,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_83 : find (dimension := 4) 59520 4 [3840,65520,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_84 : find (dimension := 4) 59520 4 [3850,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_85 : find (dimension := 4) 59520 4 [3850,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_86 : find (dimension := 4) 59520 4 [3850,65450,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_87 : find (dimension := 4) 59520 4 [3852,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_88 : find (dimension := 4) 59520 4 [3852,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_89 : find (dimension := 4) 59520 4 [3852,65484,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_90 : find (dimension := 4) 59520 4 [4112,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_91 : find (dimension := 4) 59520 4 [4352,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_92 : find (dimension := 4) 59520 4 [8224,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_93 : find (dimension := 4) 59520 4 [8704,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_94 : find (dimension := 4) 59520 4 [8738,12336,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_95 : find (dimension := 4) 59520 4 [8738,13056,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_96 : find (dimension := 4) 59520 4 [8738,17476,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_97 : find (dimension := 4) 59520 4 [8738,17476,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_98 : find (dimension := 4) 59520 4 [8738,34952,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_99 : find (dimension := 4) 59520 4 [8738,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_100 : find (dimension := 4) 59520 4 [8738,49344,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_101 : find (dimension := 4) 59520 4 [8738,52224,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_102 : find (dimension := 4) 59520 4 [8738,61166,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_103 : find (dimension := 4) 59520 4 [8874,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_104 : find (dimension := 4) 59520 4 [10794,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_105 : find (dimension := 4) 59520 4 [12288,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_106 : find (dimension := 4) 59520 4 [12336,3084,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_107 : find (dimension := 4) 59520 4 [12336,3084,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_108 : find (dimension := 4) 59520 4 [12336,8738,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_109 : find (dimension := 4) 59520 4 [12336,13056,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_110 : find (dimension := 4) 59520 4 [12336,34952,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_111 : find (dimension := 4) 59520 4 [12336,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_112 : find (dimension := 4) 59520 4 [12336,49344,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_113 : find (dimension := 4) 59520 4 [12336,52224,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_114 : find (dimension := 4) 59520 4 [12336,64764,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_115 : find (dimension := 4) 59520 4 [12528,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_116 : find (dimension := 4) 59520 4 [12850,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_117 : find (dimension := 4) 59520 4 [12850,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_118 : find (dimension := 4) 59520 4 [12850,64250,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_119 : find (dimension := 4) 59520 4 [13056,204,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_120 : find (dimension := 4) 59520 4 [13056,204,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_121 : find (dimension := 4) 59520 4 [13056,8738,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_122 : find (dimension := 4) 59520 4 [13056,12336,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_123 : find (dimension := 4) 59520 4 [13056,34952,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_124 : find (dimension := 4) 59520 4 [13056,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_125 : find (dimension := 4) 59520 4 [13056,49344,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_126 : find (dimension := 4) 59520 4 [13056,52224,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_127 : find (dimension := 4) 59520 4 [13056,65484,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_128 : find (dimension := 4) 59520 4 [13090,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_129 : find (dimension := 4) 59520 4 [13090,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_130 : find (dimension := 4) 59520 4 [13090,65450,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_131 : find (dimension := 4) 59520 4 [13104,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_132 : find (dimension := 4) 59520 4 [13104,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_133 : find (dimension := 4) 59520 4 [13104,65520,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_134 : find (dimension := 4) 59520 4 [16128,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_135 : find (dimension := 4) 59520 4 [16448,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_136 : find (dimension := 4) 59520 4 [17408,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_137 : find (dimension := 4) 59520 4 [17476,8738,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_138 : find (dimension := 4) 59520 4 [17476,8738,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_139 : find (dimension := 4) 59520 4 [17476,20560,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_140 : find (dimension := 4) 59520 4 [17476,21760,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_141 : find (dimension := 4) 59520 4 [17476,34952,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_142 : find (dimension := 4) 59520 4 [17476,41120,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_143 : find (dimension := 4) 59520 4 [17476,43520,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_144 : find (dimension := 4) 59520 4 [17476,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_145 : find (dimension := 4) 59520 4 [17476,61166,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_146 : find (dimension := 4) 59520 4 [17612,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_147 : find (dimension := 4) 59520 4 [19532,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_148 : find (dimension := 4) 59520 4 [20480,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_149 : find (dimension := 4) 59520 4 [20560,2570,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_150 : find (dimension := 4) 59520 4 [20560,2570,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_151 : find (dimension := 4) 59520 4 [20560,17476,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_152 : find (dimension := 4) 59520 4 [20560,21760,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_153 : find (dimension := 4) 59520 4 [20560,34952,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_154 : find (dimension := 4) 59520 4 [20560,41120,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_155 : find (dimension := 4) 59520 4 [20560,43520,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_156 : find (dimension := 4) 59520 4 [20560,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_157 : find (dimension := 4) 59520 4 [20560,64250,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_158 : find (dimension := 4) 59520 4 [20720,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_159 : find (dimension := 4) 59520 4 [21588,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_160 : find (dimension := 4) 59520 4 [21588,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_161 : find (dimension := 4) 59520 4 [21588,64764,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_162 : find (dimension := 4) 59520 4 [21760,170,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_163 : find (dimension := 4) 59520 4 [21760,170,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_164 : find (dimension := 4) 59520 4 [21760,17476,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_165 : find (dimension := 4) 59520 4 [21760,20560,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_166 : find (dimension := 4) 59520 4 [21760,34952,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_167 : find (dimension := 4) 59520 4 [21760,41120,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_168 : find (dimension := 4) 59520 4 [21760,43520,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_169 : find (dimension := 4) 59520 4 [21760,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_170 : find (dimension := 4) 59520 4 [21760,65450,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_171 : find (dimension := 4) 59520 4 [21828,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_172 : find (dimension := 4) 59520 4 [21828,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_173 : find (dimension := 4) 59520 4 [21828,65484,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_174 : find (dimension := 4) 59520 4 [21840,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_175 : find (dimension := 4) 59520 4 [21840,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_176 : find (dimension := 4) 59520 4 [21840,65520,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_177 : find (dimension := 4) 59520 4 [24320,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_178 : find (dimension := 4) 59520 4 [28784,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_179 : find (dimension := 4) 59520 4 [30464,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_180 : find (dimension := 4) 59520 4 [32896,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_181 : find (dimension := 4) 59520 4 [34816,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_182 : find (dimension := 4) 59520 4 [34952,8738,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_183 : find (dimension := 4) 59520 4 [34952,12336,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_184 : find (dimension := 4) 59520 4 [34952,13056,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_185 : find (dimension := 4) 59520 4 [34952,17476,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_186 : find (dimension := 4) 59520 4 [34952,20560,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_187 : find (dimension := 4) 59520 4 [34952,21760,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_188 : find (dimension := 4) 59520 4 [34952,41120,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_189 : find (dimension := 4) 59520 4 [34952,43520,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_190 : find (dimension := 4) 59520 4 [34952,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_191 : find (dimension := 4) 59520 4 [34952,49344,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_192 : find (dimension := 4) 59520 4 [34952,52224,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_193 : find (dimension := 4) 59520 4 [34952,61166,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_194 : find (dimension := 4) 59520 4 [34952,61166,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_195 : find (dimension := 4) 59520 4 [34952,61166,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_196 : find (dimension := 4) 59520 4 [34986,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_197 : find (dimension := 4) 59520 4 [35020,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_198 : find (dimension := 4) 59520 4 [35466,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_199 : find (dimension := 4) 59520 4 [35980,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_200 : find (dimension := 4) 59520 4 [40960,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_201 : find (dimension := 4) 59520 4 [41120,2570,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_202 : find (dimension := 4) 59520 4 [41120,3084,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_203 : find (dimension := 4) 59520 4 [41120,3840,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_204 : find (dimension := 4) 59520 4 [41120,17476,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_205 : find (dimension := 4) 59520 4 [41120,20560,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_206 : find (dimension := 4) 59520 4 [41120,21760,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_207 : find (dimension := 4) 59520 4 [41120,34952,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_208 : find (dimension := 4) 59520 4 [41120,43520,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_209 : find (dimension := 4) 59520 4 [41120,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_210 : find (dimension := 4) 59520 4 [41120,49344,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_211 : find (dimension := 4) 59520 4 [41120,61440,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_212 : find (dimension := 4) 59520 4 [41120,64250,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_213 : find (dimension := 4) 59520 4 [41120,64250,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_214 : find (dimension := 4) 59520 4 [41120,64250,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_215 : find (dimension := 4) 59520 4 [41130,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_216 : find (dimension := 4) 59520 4 [41200,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_217 : find (dimension := 4) 59520 4 [41634,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_218 : find (dimension := 4) 59520 4 [43176,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_219 : find (dimension := 4) 59520 4 [43176,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_220 : find (dimension := 4) 59520 4 [43176,64764,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_221 : find (dimension := 4) 59520 4 [43520,170,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_222 : find (dimension := 4) 59520 4 [43520,204,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_223 : find (dimension := 4) 59520 4 [43520,240,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_224 : find (dimension := 4) 59520 4 [43520,17476,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_225 : find (dimension := 4) 59520 4 [43520,20560,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_226 : find (dimension := 4) 59520 4 [43520,21760,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_227 : find (dimension := 4) 59520 4 [43520,34952,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_228 : find (dimension := 4) 59520 4 [43520,41120,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_229 : find (dimension := 4) 59520 4 [43520,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_230 : find (dimension := 4) 59520 4 [43520,52224,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_231 : find (dimension := 4) 59520 4 [43520,61440,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_232 : find (dimension := 4) 59520 4 [43520,65450,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_233 : find (dimension := 4) 59520 4 [43520,65450,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_234 : find (dimension := 4) 59520 4 [43520,65450,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_235 : find (dimension := 4) 59520 4 [43530,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_236 : find (dimension := 4) 59520 4 [43554,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_237 : find (dimension := 4) 59520 4 [43656,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_238 : find (dimension := 4) 59520 4 [43656,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_239 : find (dimension := 4) 59520 4 [43656,65484,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_240 : find (dimension := 4) 59520 4 [43680,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_241 : find (dimension := 4) 59520 4 [43680,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_242 : find (dimension := 4) 59520 4 [43680,65520,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_243 : find (dimension := 4) 59520 4 [43758,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_244 : find (dimension := 4) 59520 4 [43770,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_245 : find (dimension := 4) 59520 4 [44718,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_246 : find (dimension := 4) 59520 4 [44800,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_247 : find (dimension := 4) 59520 4 [44970,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_248 : find (dimension := 4) 59520 4 [45232,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_249 : find (dimension := 4) 59520 4 [47802,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_250 : find (dimension := 4) 59520 4 [47872,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_251 : find (dimension := 4) 59520 4 [48042,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_252 : find (dimension := 4) 59520 4 [49152,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_253 : find (dimension := 4) 59520 4 [49344,2570,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_254 : find (dimension := 4) 59520 4 [49344,3084,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_255 : find (dimension := 4) 59520 4 [49344,3840,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_256 : find (dimension := 4) 59520 4 [49344,8738,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_257 : find (dimension := 4) 59520 4 [49344,12336,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_258 : find (dimension := 4) 59520 4 [49344,13056,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_259 : find (dimension := 4) 59520 4 [49344,34952,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_260 : find (dimension := 4) 59520 4 [49344,41120,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_261 : find (dimension := 4) 59520 4 [49344,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_262 : find (dimension := 4) 59520 4 [49344,52224,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_263 : find (dimension := 4) 59520 4 [49344,61440,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_264 : find (dimension := 4) 59520 4 [49344,64764,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_265 : find (dimension := 4) 59520 4 [49344,64764,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_266 : find (dimension := 4) 59520 4 [49344,64764,43690,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_267 : find (dimension := 4) 59520 4 [49356,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_268 : find (dimension := 4) 59520 4 [49392,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_269 : find (dimension := 4) 59520 4 [50372,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_270 : find (dimension := 4) 59520 4 [51400,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_271 : find (dimension := 4) 59520 4 [51400,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_272 : find (dimension := 4) 59520 4 [51400,64250,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_273 : find (dimension := 4) 59520 4 [52224,170,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_274 : find (dimension := 4) 59520 4 [52224,204,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_275 : find (dimension := 4) 59520 4 [52224,240,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_276 : find (dimension := 4) 59520 4 [52224,8738,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_277 : find (dimension := 4) 59520 4 [52224,12336,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_278 : find (dimension := 4) 59520 4 [52224,13056,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_279 : find (dimension := 4) 59520 4 [52224,34952,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_280 : find (dimension := 4) 59520 4 [52224,43520,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_281 : find (dimension := 4) 59520 4 [52224,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_282 : find (dimension := 4) 59520 4 [52224,49344,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_283 : find (dimension := 4) 59520 4 [52224,61440,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_284 : find (dimension := 4) 59520 4 [52224,65484,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_285 : find (dimension := 4) 59520 4 [52224,65484,43690,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_286 : find (dimension := 4) 59520 4 [52224,65484,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_287 : find (dimension := 4) 59520 4 [52236,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_288 : find (dimension := 4) 59520 4 [52292,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_289 : find (dimension := 4) 59520 4 [52360,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_290 : find (dimension := 4) 59520 4 [52360,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_291 : find (dimension := 4) 59520 4 [52360,65450,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_292 : find (dimension := 4) 59520 4 [52416,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_293 : find (dimension := 4) 59520 4 [52416,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_294 : find (dimension := 4) 59520 4 [52416,65520,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_295 : find (dimension := 4) 59520 4 [52462,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_296 : find (dimension := 4) 59520 4 [52476,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_297 : find (dimension := 4) 59520 4 [52942,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_298 : find (dimension := 4) 59520 4 [52992,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_299 : find (dimension := 4) 59520 4 [53196,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_300 : find (dimension := 4) 59520 4 [53456,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_301 : find (dimension := 4) 59520 4 [56540,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_302 : find (dimension := 4) 59520 4 [56576,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_303 : find (dimension := 4) 59520 4 [56780,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_304 : find (dimension := 4) 59520 4 [57568,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_305 : find (dimension := 4) 59520 4 [57568,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_306 : find (dimension := 4) 59520 4 [57568,61166,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_307 : find (dimension := 4) 59520 4 [60138,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_308 : find (dimension := 4) 59520 4 [60652,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_309 : find (dimension := 4) 59520 4 [60928,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_310 : find (dimension := 4) 59520 4 [60928,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_311 : find (dimension := 4) 59520 4 [60928,61166,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_312 : find (dimension := 4) 59520 4 [61098,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_313 : find (dimension := 4) 59520 4 [61132,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_314 : find (dimension := 4) 59520 4 [61166,8738,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_315 : find (dimension := 4) 59520 4 [61166,17476,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_316 : find (dimension := 4) 59520 4 [61166,34952,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_317 : find (dimension := 4) 59520 4 [61166,34952,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_318 : find (dimension := 4) 59520 4 [61166,34952,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_319 : find (dimension := 4) 59520 4 [61166,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_320 : find (dimension := 4) 59520 4 [61440,170,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_321 : find (dimension := 4) 59520 4 [61440,204,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_322 : find (dimension := 4) 59520 4 [61440,240,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_323 : find (dimension := 4) 59520 4 [61440,2570,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_324 : find (dimension := 4) 59520 4 [61440,3084,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_325 : find (dimension := 4) 59520 4 [61440,3840,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_326 : find (dimension := 4) 59520 4 [61440,41120,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_327 : find (dimension := 4) 59520 4 [61440,43520,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_328 : find (dimension := 4) 59520 4 [61440,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_329 : find (dimension := 4) 59520 4 [61440,49344,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_330 : find (dimension := 4) 59520 4 [61440,52224,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_331 : find (dimension := 4) 59520 4 [61440,65520,43690,52428] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_332 : find (dimension := 4) 59520 4 [61440,65520,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_333 : find (dimension := 4) 59520 4 [61440,65520,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_334 : find (dimension := 4) 59520 4 [61488,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_335 : find (dimension := 4) 59520 4 [61520,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_336 : find (dimension := 4) 59520 4 [61600,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_337 : find (dimension := 4) 59520 4 [61600,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_338 : find (dimension := 4) 59520 4 [61600,65450,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_339 : find (dimension := 4) 59520 4 [61632,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_340 : find (dimension := 4) 59520 4 [61632,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_341 : find (dimension := 4) 59520 4 [61632,65484,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_342 : find (dimension := 4) 59520 4 [61690,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_343 : find (dimension := 4) 59520 4 [61692,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_344 : find (dimension := 4) 59520 4 [62194,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_345 : find (dimension := 4) 59520 4 [62208,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_346 : find (dimension := 4) 59520 4 [62448,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_347 : find (dimension := 4) 59520 4 [62708,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_348 : find (dimension := 4) 59520 4 [62720,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_349 : find (dimension := 4) 59520 4 [62960,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_350 : find (dimension := 4) 59520 4 [63736,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_351 : find (dimension := 4) 59520 4 [64000,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_352 : find (dimension := 4) 59520 4 [64000,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_353 : find (dimension := 4) 59520 4 [64000,64250,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_354 : find (dimension := 4) 59520 4 [64170,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_355 : find (dimension := 4) 59520 4 [64240,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_356 : find (dimension := 4) 59520 4 [64250,2570,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_357 : find (dimension := 4) 59520 4 [64250,20560,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_358 : find (dimension := 4) 59520 4 [64250,41120,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_359 : find (dimension := 4) 59520 4 [64250,41120,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_360 : find (dimension := 4) 59520 4 [64250,41120,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_361 : find (dimension := 4) 59520 4 [64250,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_362 : find (dimension := 4) 59520 4 [64512,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_363 : find (dimension := 4) 59520 4 [64512,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_364 : find (dimension := 4) 59520 4 [64512,64764,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_365 : find (dimension := 4) 59520 4 [64716,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_366 : find (dimension := 4) 59520 4 [64752,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_367 : find (dimension := 4) 59520 4 [64764,3084,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_368 : find (dimension := 4) 59520 4 [64764,12336,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_369 : find (dimension := 4) 59520 4 [64764,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_370 : find (dimension := 4) 59520 4 [64764,49344,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_371 : find (dimension := 4) 59520 4 [64764,49344,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_372 : find (dimension := 4) 59520 4 [64764,49344,43690,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_373 : find (dimension := 4) 59520 4 [65278,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_374 : find (dimension := 4) 59520 4 [65290,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_375 : find (dimension := 4) 59520 4 [65292,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_376 : find (dimension := 4) 59520 4 [65314,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_377 : find (dimension := 4) 59520 4 [65328,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_378 : find (dimension := 4) 59520 4 [65348,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_379 : find (dimension := 4) 59520 4 [65360,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_380 : find (dimension := 4) 59520 4 [65416,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_381 : find (dimension := 4) 59520 4 [65440,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_382 : find (dimension := 4) 59520 4 [65450,170,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_383 : find (dimension := 4) 59520 4 [65450,21760,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_384 : find (dimension := 4) 59520 4 [65450,43520,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_385 : find (dimension := 4) 59520 4 [65450,43520,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_386 : find (dimension := 4) 59520 4 [65450,43520,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_387 : find (dimension := 4) 59520 4 [65450,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_388 : find (dimension := 4) 59520 4 [65472,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_389 : find (dimension := 4) 59520 4 [65484,204,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_390 : find (dimension := 4) 59520 4 [65484,13056,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_391 : find (dimension := 4) 59520 4 [65484,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_392 : find (dimension := 4) 59520 4 [65484,52224,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_393 : find (dimension := 4) 59520 4 [65484,52224,43690,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_394 : find (dimension := 4) 59520 4 [65484,52224,43690,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_395 : find (dimension := 4) 59520 4 [65518,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_396 : find (dimension := 4) 59520 4 [65520,240,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_397 : find (dimension := 4) 59520 4 [65520,3840,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_398 : find (dimension := 4) 59520 4 [65520,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_399 : find (dimension := 4) 59520 4 [65520,61440,43690,52428] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_400 : find (dimension := 4) 59520 4 [65520,61440,43690,52428,61680] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_401 : find (dimension := 4) 59520 4 [65520,61440,43690,52428,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_402 : find (dimension := 4) 59520 4 [65530,43690,52428,61680,65280] = false := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem n3_2_403 : find (dimension := 4) 59520 4 [65532,43690,52428,61680,65280] = false := by
  decide +kernel
private theorem n3_1_0 : find (dimension := 4) 59520 5 [170,43690,52428,61680,65280] = false := by
  apply blocked_sound (known := [[10,43690,52428,61680,65280],[34,43690,52428,61680,65280],[136,43690,52428,61680,65280],[160,43690,52428,61680,65280],[204,170,43690,52428,61680],[240,170,43690,52428,61680],[21760,170,43690,52428,61680],[21760,170,52428,61680,65280],[43520,170,52428,61680,65280],[43520,43690,52428,61680,65280],[52224,170,43690,52428,61680],[52292,43690,52428,61680,65280],[52462,43690,52428,61680,65280],[61440,170,43690,52428,61680],[61520,43690,52428,61680,65280],[61690,43690,52428,61680,65280],[65450,170,43690,52428,61680],[65450,43690,52428,61680,65280]])
  · decide +kernel
  · intro M hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact n3_2_0
    · exact n3_2_2
    · exact n3_2_6
    · exact n3_2_7
    · exact n3_2_18
    · exact n3_2_30
    · exact n3_2_162
    · exact n3_2_163
    · exact n3_2_221
    · exact n3_2_229
    · exact n3_2_273
    · exact n3_2_288
    · exact n3_2_295
    · exact n3_2_320
    · exact n3_2_335
    · exact n3_2_342
    · exact n3_2_382
    · exact n3_2_387
private theorem n3_1_1 : find (dimension := 4) 59520 5 [204,43690,52428,61680,65280] = false := by
  apply blocked_sound (known := [[12,43690,52428,61680,65280],[68,43690,52428,61680,65280],[136,43690,52428,61680,65280],[170,204,43690,52428,61680],[192,43690,52428,61680,65280],[240,204,43690,52428,61680],[13056,204,43690,52428,61680],[13056,204,43690,61680,65280],[43520,204,43690,52428,61680],[43554,43690,52428,61680,65280],[43758,43690,52428,61680,65280],[52224,204,43690,61680,65280],[52224,43690,52428,61680,65280],[61440,204,43690,52428,61680],[61488,43690,52428,61680,65280],[61692,43690,52428,61680,65280],[65484,204,43690,52428,61680],[65484,43690,52428,61680,65280]])
  · decide +kernel
  · intro M hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact n3_2_1
    · exact n3_2_4
    · exact n3_2_6
    · exact n3_2_8
    · exact n3_2_17
    · exact n3_2_31
    · exact n3_2_119
    · exact n3_2_120
    · exact n3_2_222
    · exact n3_2_236
    · exact n3_2_243
    · exact n3_2_274
    · exact n3_2_281
    · exact n3_2_321
    · exact n3_2_334
    · exact n3_2_343
    · exact n3_2_389
    · exact n3_2_391
private theorem n3_1_2 : find (dimension := 4) 59520 5 [240,43690,52428,61680,65280] = false := by
  apply blocked_sound (known := [[48,43690,52428,61680,65280],[80,43690,52428,61680,65280],[160,43690,52428,61680,65280],[170,240,43690,52428,61680],[192,43690,52428,61680,65280],[204,240,43690,52428,61680],[3840,240,43690,52428,61680],[3840,240,43690,52428,65280],[43520,240,43690,52428,61680],[43530,43690,52428,61680,65280],[43770,43690,52428,61680,65280],[52224,240,43690,52428,61680],[52236,43690,52428,61680,65280],[52476,43690,52428,61680,65280],[61440,240,43690,52428,65280],[61440,43690,52428,61680,65280],[65520,240,43690,52428,61680],[65520,43690,52428,61680,65280]])
  · decide +kernel
  · intro M hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact n3_2_3
    · exact n3_2_5
    · exact n3_2_7
    · exact n3_2_9
    · exact n3_2_17
    · exact n3_2_19
    · exact n3_2_75
    · exact n3_2_76
    · exact n3_2_223
    · exact n3_2_235
    · exact n3_2_244
    · exact n3_2_275
    · exact n3_2_287
    · exact n3_2_296
    · exact n3_2_322
    · exact n3_2_328
    · exact n3_2_396
    · exact n3_2_398
private theorem n3_1_3 : find (dimension := 4) 59520 5 [2570,43690,52428,61680,65280] = false := by
  apply blocked_sound (known := [[10,43690,52428,61680,65280],[514,43690,52428,61680,65280],[2056,43690,52428,61680,65280],[2560,43690,52428,61680,65280],[3084,2570,43690,52428,65280],[3840,2570,43690,52428,65280],[20560,2570,43690,52428,65280],[20560,2570,52428,61680,65280],[41120,2570,52428,61680,65280],[41120,43690,52428,61680,65280],[49344,2570,43690,52428,65280],[50372,43690,52428,61680,65280],[52942,43690,52428,61680,65280],[61440,2570,43690,52428,65280],[62720,43690,52428,61680,65280],[64250,2570,43690,52428,65280],[64250,43690,52428,61680,65280],[65290,43690,52428,61680,65280]])
  · decide +kernel
  · intro M hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact n3_2_0
    · exact n3_2_45
    · exact n3_2_49
    · exact n3_2_50
    · exact n3_2_62
    · exact n3_2_77
    · exact n3_2_149
    · exact n3_2_150
    · exact n3_2_201
    · exact n3_2_209
    · exact n3_2_253
    · exact n3_2_269
    · exact n3_2_297
    · exact n3_2_323
    · exact n3_2_348
    · exact n3_2_356
    · exact n3_2_361
    · exact n3_2_374
private theorem n3_1_4 : find (dimension := 4) 59520 5 [3084,43690,52428,61680,65280] = false := by
  apply blocked_sound (known := [[12,43690,52428,61680,65280],[1028,43690,52428,61680,65280],[2056,43690,52428,61680,65280],[2570,3084,43690,52428,65280],[3072,43690,52428,61680,65280],[3840,3084,43690,52428,65280],[12336,3084,43690,52428,65280],[12336,3084,43690,61680,65280],[41120,3084,43690,52428,65280],[41634,43690,52428,61680,65280],[44718,43690,52428,61680,65280],[49344,3084,43690,61680,65280],[49344,43690,52428,61680,65280],[61440,3084,43690,52428,65280],[62208,43690,52428,61680,65280],[64764,3084,43690,52428,65280],[64764,43690,52428,61680,65280],[65292,43690,52428,61680,65280]])
  · decide +kernel
  · intro M hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact n3_2_1
    · exact n3_2_47
    · exact n3_2_49
    · exact n3_2_51
    · exact n3_2_61
    · exact n3_2_78
    · exact n3_2_106
    · exact n3_2_107
    · exact n3_2_202
    · exact n3_2_217
    · exact n3_2_245
    · exact n3_2_254
    · exact n3_2_261
    · exact n3_2_324
    · exact n3_2_345
    · exact n3_2_367
    · exact n3_2_369
    · exact n3_2_375
private theorem n3_1_5 : find (dimension := 4) 59520 5 [3840,43690,52428,61680,65280] = false := by
  apply blocked_sound (known := [[240,3840,43690,52428,61680],[240,3840,43690,52428,65280],[768,43690,52428,61680,65280],[1280,43690,52428,61680,65280],[2560,43690,52428,61680,65280],[2570,3840,43690,52428,65280],[3072,43690,52428,61680,65280],[3084,3840,43690,52428,65280],[41120,3840,43690,52428,65280],[41130,43690,52428,61680,65280],[44970,43690,52428,61680,65280],[49344,3840,43690,52428,65280],[49356,43690,52428,61680,65280],[53196,43690,52428,61680,65280],[61440,3840,43690,52428,61680],[61440,43690,52428,61680,65280],[65520,3840,43690,52428,65280],[65520,43690,52428,61680,65280]])
  · decide +kernel
  · intro M hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact n3_2_32
    · exact n3_2_33
    · exact n3_2_46
    · exact n3_2_48
    · exact n3_2_50
    · exact n3_2_52
    · exact n3_2_61
    · exact n3_2_63
    · exact n3_2_203
    · exact n3_2_215
    · exact n3_2_247
    · exact n3_2_255
    · exact n3_2_267
    · exact n3_2_299
    · exact n3_2_325
    · exact n3_2_328
    · exact n3_2_397
    · exact n3_2_398
private theorem n3_1_6 : find (dimension := 4) 59520 5 [8738,43690,52428,61680,65280] = false := by
  apply blocked_sound (known := [[34,43690,52428,61680,65280],[514,43690,52428,61680,65280],[8224,43690,52428,61680,65280],[8704,43690,52428,61680,65280],[12336,8738,43690,61680,65280],[13056,8738,43690,61680,65280],[17476,8738,43690,61680,65280],[17476,8738,52428,61680,65280],[34952,8738,52428,61680,65280],[34952,43690,52428,61680,65280],[49344,8738,43690,61680,65280],[52224,8738,43690,61680,65280],[53456,43690,52428,61680,65280],[56576,43690,52428,61680,65280],[61166,8738,43690,61680,65280],[61166,43690,52428,61680,65280],[62194,43690,52428,61680,65280],[65314,43690,52428,61680,65280]])
  · decide +kernel
  · intro M hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact n3_2_2
    · exact n3_2_45
    · exact n3_2_92
    · exact n3_2_93
    · exact n3_2_108
    · exact n3_2_121
    · exact n3_2_137
    · exact n3_2_138
    · exact n3_2_182
    · exact n3_2_190
    · exact n3_2_256
    · exact n3_2_276
    · exact n3_2_300
    · exact n3_2_302
    · exact n3_2_314
    · exact n3_2_319
    · exact n3_2_344
    · exact n3_2_376
private theorem n3_1_7 : find (dimension := 4) 59520 5 [12336,43690,52428,61680,65280] = false := by
  apply blocked_sound (known := [[48,43690,52428,61680,65280],[3084,12336,43690,52428,65280],[3084,12336,43690,61680,65280],[4112,43690,52428,61680,65280],[8224,43690,52428,61680,65280],[8738,12336,43690,61680,65280],[12288,43690,52428,61680,65280],[13056,12336,43690,61680,65280],[34952,12336,43690,61680,65280],[35466,43690,52428,61680,65280],[47802,43690,52428,61680,65280],[49344,12336,43690,52428,65280],[49344,43690,52428,61680,65280],[52224,12336,43690,61680,65280],[52992,43690,52428,61680,65280],[64764,12336,43690,61680,65280],[64764,43690,52428,61680,65280],[65328,43690,52428,61680,65280]])
  · decide +kernel
  · intro M hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact n3_2_3
    · exact n3_2_64
    · exact n3_2_65
    · exact n3_2_90
    · exact n3_2_92
    · exact n3_2_94
    · exact n3_2_105
    · exact n3_2_122
    · exact n3_2_183
    · exact n3_2_198
    · exact n3_2_249
    · exact n3_2_257
    · exact n3_2_261
    · exact n3_2_277
    · exact n3_2_298
    · exact n3_2_368
    · exact n3_2_369
    · exact n3_2_377
private theorem n3_1_8 : find (dimension := 4) 59520 5 [13056,43690,52428,61680,65280] = false := by
  apply blocked_sound (known := [[204,13056,43690,52428,61680],[204,13056,43690,61680,65280],[768,43690,52428,61680,65280],[4352,43690,52428,61680,65280],[8704,43690,52428,61680,65280],[8738,13056,43690,61680,65280],[12288,43690,52428,61680,65280],[12336,13056,43690,61680,65280],[34952,13056,43690,61680,65280],[34986,43690,52428,61680,65280],[48042,43690,52428,61680,65280],[49344,13056,43690,61680,65280],[49392,43690,52428,61680,65280],[52224,13056,43690,52428,61680],[52224,43690,52428,61680,65280],[62448,43690,52428,61680,65280],[65484,13056,43690,61680,65280],[65484,43690,52428,61680,65280]])
  · decide +kernel
  · intro M hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact n3_2_20
    · exact n3_2_21
    · exact n3_2_46
    · exact n3_2_91
    · exact n3_2_93
    · exact n3_2_95
    · exact n3_2_105
    · exact n3_2_109
    · exact n3_2_184
    · exact n3_2_196
    · exact n3_2_251
    · exact n3_2_258
    · exact n3_2_268
    · exact n3_2_278
    · exact n3_2_281
    · exact n3_2_346
    · exact n3_2_390
    · exact n3_2_391
private theorem n3_1_9 : find (dimension := 4) 59520 5 [17476,43690,52428,61680,65280] = false := by
  apply blocked_sound (known := [[68,43690,52428,61680,65280],[1028,43690,52428,61680,65280],[8738,17476,43690,61680,65280],[8738,17476,52428,61680,65280],[16448,43690,52428,61680,65280],[17408,43690,52428,61680,65280],[20560,17476,52428,61680,65280],[21760,17476,52428,61680,65280],[34952,17476,43690,61680,65280],[34952,43690,52428,61680,65280],[41120,17476,52428,61680,65280],[43520,17476,52428,61680,65280],[45232,43690,52428,61680,65280],[47872,43690,52428,61680,65280],[61166,17476,52428,61680,65280],[61166,43690,52428,61680,65280],[62708,43690,52428,61680,65280],[65348,43690,52428,61680,65280]])
  · decide +kernel
  · intro M hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact n3_2_4
    · exact n3_2_47
    · exact n3_2_96
    · exact n3_2_97
    · exact n3_2_135
    · exact n3_2_136
    · exact n3_2_151
    · exact n3_2_164
    · exact n3_2_185
    · exact n3_2_190
    · exact n3_2_204
    · exact n3_2_224
    · exact n3_2_248
    · exact n3_2_250
    · exact n3_2_315
    · exact n3_2_319
    · exact n3_2_347
    · exact n3_2_378
private theorem n3_1_10 : find (dimension := 4) 59520 5 [20560,43690,52428,61680,65280] = false := by
  apply blocked_sound (known := [[80,43690,52428,61680,65280],[2570,20560,43690,52428,65280],[2570,20560,52428,61680,65280],[4112,43690,52428,61680,65280],[16448,43690,52428,61680,65280],[17476,20560,52428,61680,65280],[20480,43690,52428,61680,65280],[21760,20560,52428,61680,65280],[34952,20560,52428,61680,65280],[35980,43690,52428,61680,65280],[41120,20560,43690,52428,65280],[41120,43690,52428,61680,65280],[43520,20560,52428,61680,65280],[44800,43690,52428,61680,65280],[56540,43690,52428,61680,65280],[64250,20560,52428,61680,65280],[64250,43690,52428,61680,65280],[65360,43690,52428,61680,65280]])
  · decide +kernel
  · intro M hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact n3_2_5
    · exact n3_2_53
    · exact n3_2_54
    · exact n3_2_90
    · exact n3_2_135
    · exact n3_2_139
    · exact n3_2_148
    · exact n3_2_165
    · exact n3_2_186
    · exact n3_2_199
    · exact n3_2_205
    · exact n3_2_209
    · exact n3_2_225
    · exact n3_2_246
    · exact n3_2_301
    · exact n3_2_357
    · exact n3_2_361
    · exact n3_2_379
private theorem n3_1_11 : find (dimension := 4) 59520 5 [21760,43690,52428,61680,65280] = false := by
  apply blocked_sound (known := [[170,21760,43690,52428,61680],[170,21760,52428,61680,65280],[1280,43690,52428,61680,65280],[4352,43690,52428,61680,65280],[17408,43690,52428,61680,65280],[17476,21760,52428,61680,65280],[20480,43690,52428,61680,65280],[20560,21760,52428,61680,65280],[34952,21760,52428,61680,65280],[35020,43690,52428,61680,65280],[41120,21760,52428,61680,65280],[41200,43690,52428,61680,65280],[43520,21760,43690,52428,61680],[43520,43690,52428,61680,65280],[56780,43690,52428,61680,65280],[62960,43690,52428,61680,65280],[65450,21760,52428,61680,65280],[65450,43690,52428,61680,65280]])
  · decide +kernel
  · intro M hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact n3_2_10
    · exact n3_2_11
    · exact n3_2_48
    · exact n3_2_91
    · exact n3_2_136
    · exact n3_2_140
    · exact n3_2_148
    · exact n3_2_152
    · exact n3_2_187
    · exact n3_2_197
    · exact n3_2_206
    · exact n3_2_216
    · exact n3_2_226
    · exact n3_2_229
    · exact n3_2_303
    · exact n3_2_349
    · exact n3_2_383
    · exact n3_2_387
private theorem n3_1_12 : find (dimension := 4) 59520 5 [34952,43690,52428,61680,65280] = false := by
  apply blocked_sound (known := [[136,43690,52428,61680,65280],[2056,43690,52428,61680,65280],[8738,34952,52428,61680,65280],[8738,43690,52428,61680,65280],[12336,34952,43690,61680,65280],[13056,34952,43690,61680,65280],[17476,34952,43690,61680,65280],[17476,43690,52428,61680,65280],[20560,34952,52428,61680,65280],[21760,34952,52428,61680,65280],[28784,43690,52428,61680,65280],[30464,43690,52428,61680,65280],[32896,43690,52428,61680,65280],[34816,43690,52428,61680,65280],[41120,34952,52428,61680,65280],[43520,34952,52428,61680,65280],[49344,34952,43690,61680,65280],[52224,34952,43690,61680,65280],[61166,34952,43690,61680,65280],[61166,34952,52428,61680,65280],[61166,34952,61680,65280],[63736,43690,52428,61680,65280],[65416,43690,52428,61680,65280]])
  · decide +kernel
  · intro M hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact n3_2_6
    · exact n3_2_49
    · exact n3_2_98
    · exact n3_2_99
    · exact n3_2_110
    · exact n3_2_123
    · exact n3_2_141
    · exact n3_2_144
    · exact n3_2_153
    · exact n3_2_166
    · exact n3_2_178
    · exact n3_2_179
    · exact n3_2_180
    · exact n3_2_181
    · exact n3_2_207
    · exact n3_2_227
    · exact n3_2_259
    · exact n3_2_279
    · exact n3_2_316
    · exact n3_2_317
    · exact n3_2_318
    · exact n3_2_350
    · exact n3_2_380
private theorem n3_1_13 : find (dimension := 4) 59520 5 [41120,43690,52428,61680,65280] = false := by
  apply blocked_sound (known := [[160,43690,52428,61680,65280],[2570,41120,52428,61680,65280],[2570,43690,52428,61680,65280],[3084,41120,43690,52428,65280],[3840,41120,43690,52428,65280],[8224,43690,52428,61680,65280],[17476,41120,52428,61680,65280],[19532,43690,52428,61680,65280],[20560,41120,43690,52428,65280],[20560,43690,52428,61680,65280],[21760,41120,52428,61680,65280],[24320,43690,52428,61680,65280],[32896,43690,52428,61680,65280],[34952,41120,52428,61680,65280],[40960,43690,52428,61680,65280],[43520,41120,52428,61680,65280],[49344,41120,43690,52428,65280],[60652,43690,52428,61680,65280],[61440,41120,43690,52428,65280],[64250,41120,43690,52428,65280],[64250,41120,52428,61680,65280],[64250,41120,52428,65280],[65440,43690,52428,61680,65280]])
  · decide +kernel
  · intro M hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact n3_2_7
    · exact n3_2_55
    · exact n3_2_56
    · exact n3_2_66
    · exact n3_2_79
    · exact n3_2_92
    · exact n3_2_142
    · exact n3_2_147
    · exact n3_2_154
    · exact n3_2_156
    · exact n3_2_167
    · exact n3_2_177
    · exact n3_2_180
    · exact n3_2_188
    · exact n3_2_200
    · exact n3_2_228
    · exact n3_2_260
    · exact n3_2_308
    · exact n3_2_326
    · exact n3_2_358
    · exact n3_2_359
    · exact n3_2_360
    · exact n3_2_381
private theorem n3_1_14 : find (dimension := 4) 59520 5 [43520,43690,52428,61680,65280] = false := by
  apply blocked_sound (known := [[170,43520,52428,61680,65280],[170,43690,52428,61680,65280],[204,43520,43690,52428,61680],[240,43520,43690,52428,61680],[2560,43690,52428,61680,65280],[8704,43690,52428,61680,65280],[17476,43520,52428,61680,65280],[17612,43690,52428,61680,65280],[20560,43520,52428,61680,65280],[20720,43690,52428,61680,65280],[21760,43520,43690,52428,61680],[21760,43690,52428,61680,65280],[34816,43690,52428,61680,65280],[34952,43520,52428,61680,65280],[40960,43690,52428,61680,65280],[41120,43520,52428,61680,65280],[52224,43520,43690,52428,61680],[61132,43690,52428,61680,65280],[61440,43520,43690,52428,61680],[64240,43690,52428,61680,65280],[65450,43520,43690,52428,61680],[65450,43520,52428,61680],[65450,43520,52428,61680,65280]])
  · decide +kernel
  · intro M hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact n3_2_12
    · exact n3_2_13
    · exact n3_2_22
    · exact n3_2_34
    · exact n3_2_50
    · exact n3_2_93
    · exact n3_2_143
    · exact n3_2_146
    · exact n3_2_155
    · exact n3_2_158
    · exact n3_2_168
    · exact n3_2_169
    · exact n3_2_181
    · exact n3_2_189
    · exact n3_2_200
    · exact n3_2_208
    · exact n3_2_280
    · exact n3_2_313
    · exact n3_2_327
    · exact n3_2_355
    · exact n3_2_384
    · exact n3_2_385
    · exact n3_2_386
private theorem n3_1_15 : find (dimension := 4) 59520 5 [49344,43690,52428,61680,65280] = false := by
  apply blocked_sound (known := [[192,43690,52428,61680,65280],[2570,49344,43690,52428,65280],[3084,43690,52428,61680,65280],[3084,49344,43690,61680,65280],[3840,49344,43690,52428,65280],[8738,49344,43690,61680,65280],[10794,43690,52428,61680,65280],[12336,43690,52428,61680,65280],[12336,49344,43690,52428,65280],[13056,49344,43690,61680,65280],[16128,43690,52428,61680,65280],[16448,43690,52428,61680,65280],[32896,43690,52428,61680,65280],[34952,49344,43690,61680,65280],[41120,49344,43690,52428,65280],[49152,43690,52428,61680,65280],[52224,49344,43690,61680,65280],[60138,43690,52428,61680,65280],[61440,49344,43690,52428,65280],[64764,49344,43690,52428,65280],[64764,49344,43690,61680,65280],[64764,49344,43690,65280],[65472,43690,52428,61680,65280]])
  · decide +kernel
  · intro M hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact n3_2_17
    · exact n3_2_57
    · exact n3_2_67
    · exact n3_2_68
    · exact n3_2_81
    · exact n3_2_100
    · exact n3_2_104
    · exact n3_2_111
    · exact n3_2_112
    · exact n3_2_125
    · exact n3_2_134
    · exact n3_2_135
    · exact n3_2_180
    · exact n3_2_191
    · exact n3_2_210
    · exact n3_2_252
    · exact n3_2_282
    · exact n3_2_307
    · exact n3_2_329
    · exact n3_2_370
    · exact n3_2_371
    · exact n3_2_372
    · exact n3_2_388
private theorem n3_1_16 : find (dimension := 4) 59520 5 [52224,43690,52428,61680,65280] = false := by
  apply blocked_sound (known := [[170,52224,43690,52428,61680],[204,43690,52428,61680,65280],[204,52224,43690,61680,65280],[240,52224,43690,52428,61680],[3072,43690,52428,61680,65280],[8738,52224,43690,61680,65280],[8874,43690,52428,61680,65280],[12336,52224,43690,61680,65280],[12528,43690,52428,61680,65280],[13056,43690,52428,61680,65280],[13056,52224,43690,52428,61680],[17408,43690,52428,61680,65280],[34816,43690,52428,61680,65280],[34952,52224,43690,61680,65280],[43520,52224,43690,52428,61680],[49152,43690,52428,61680,65280],[49344,52224,43690,61680,65280],[61098,43690,52428,61680,65280],[61440,52224,43690,52428,61680],[64752,43690,52428,61680,65280],[65484,52224,43690,52428,61680],[65484,52224,43690,61680],[65484,52224,43690,61680,65280]])
  · decide +kernel
  · intro M hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact n3_2_14
    · exact n3_2_23
    · exact n3_2_24
    · exact n3_2_36
    · exact n3_2_61
    · exact n3_2_101
    · exact n3_2_103
    · exact n3_2_113
    · exact n3_2_115
    · exact n3_2_124
    · exact n3_2_126
    · exact n3_2_136
    · exact n3_2_181
    · exact n3_2_192
    · exact n3_2_230
    · exact n3_2_252
    · exact n3_2_262
    · exact n3_2_312
    · exact n3_2_330
    · exact n3_2_366
    · exact n3_2_392
    · exact n3_2_393
    · exact n3_2_394
private theorem n3_1_17 : find (dimension := 4) 59520 5 [61166,43690,52428,61680,65280] = false := by
  apply blocked_sound (known := [[238,43690,52428,61680],[238,43690,52428,61680,65280],[238,61166,43690,52428,61680],[3598,43690,52428,61680,65280],[3598,43690,52428,65280],[3598,61166,43690,52428,65280],[4112,43690,52428,61680,65280],[4352,43690,52428,61680,65280],[8738,43690,52428,61680,65280],[8738,61166,43690,61680,65280],[17476,43690,52428,61680,65280],[17476,61166,52428,61680,65280],[34952,61166,43690,61680,65280],[34952,61166,52428,61680,65280],[34952,61166,61680,65280],[57568,43690,52428,61680,65280],[57568,43690,52428,65280],[57568,61166,43690,52428,65280],[60928,43690,52428,61680],[60928,43690,52428,61680,65280],[60928,61166,43690,52428,61680],[65278,43690,52428,61680,65280],[65518,43690,52428,61680,65280]])
  · decide +kernel
  · intro M hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact n3_2_27
    · exact n3_2_28
    · exact n3_2_29
    · exact n3_2_72
    · exact n3_2_73
    · exact n3_2_74
    · exact n3_2_90
    · exact n3_2_91
    · exact n3_2_99
    · exact n3_2_102
    · exact n3_2_144
    · exact n3_2_145
    · exact n3_2_193
    · exact n3_2_194
    · exact n3_2_195
    · exact n3_2_304
    · exact n3_2_305
    · exact n3_2_306
    · exact n3_2_309
    · exact n3_2_310
    · exact n3_2_311
    · exact n3_2_373
    · exact n3_2_395
private theorem n3_1_18 : find (dimension := 4) 59520 5 [61440,43690,52428,61680,65280] = false := by
  apply blocked_sound (known := [[170,61440,43690,52428,61680],[204,61440,43690,52428,61680],[240,43690,52428,61680,65280],[240,61440,43690,52428,65280],[2570,61440,43690,52428,65280],[2730,43690,52428,61680,65280],[3084,61440,43690,52428,65280],[3276,43690,52428,61680,65280],[3840,43690,52428,61680,65280],[3840,61440,43690,52428,61680],[12288,43690,52428,61680,65280],[20480,43690,52428,61680,65280],[40960,43690,52428,61680,65280],[41120,61440,43690,52428,65280],[43520,61440,43690,52428,61680],[49152,43690,52428,61680,65280],[49344,61440,43690,52428,65280],[52224,61440,43690,52428,61680],[64170,43690,52428,61680,65280],[64716,43690,52428,61680,65280],[65520,61440,43690,52428],[65520,61440,43690,52428,61680],[65520,61440,43690,52428,65280]])
  · decide +kernel
  · intro M hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact n3_2_15
    · exact n3_2_25
    · exact n3_2_35
    · exact n3_2_37
    · exact n3_2_58
    · exact n3_2_60
    · exact n3_2_69
    · exact n3_2_71
    · exact n3_2_80
    · exact n3_2_82
    · exact n3_2_105
    · exact n3_2_148
    · exact n3_2_200
    · exact n3_2_211
    · exact n3_2_231
    · exact n3_2_252
    · exact n3_2_263
    · exact n3_2_283
    · exact n3_2_354
    · exact n3_2_365
    · exact n3_2_399
    · exact n3_2_400
    · exact n3_2_401
private theorem n3_1_19 : find (dimension := 4) 59520 5 [64250,43690,52428,61680,65280] = false := by
  apply blocked_sound (known := [[250,43690,52428,61680],[250,43690,52428,61680,65280],[250,64250,43690,52428,61680],[1028,43690,52428,61680,65280],[1280,43690,52428,61680,65280],[2570,43690,52428,61680,65280],[2570,64250,43690,52428,65280],[12850,43690,52428,61680,65280],[12850,43690,61680,65280],[12850,64250,43690,61680,65280],[20560,43690,52428,61680,65280],[20560,64250,52428,61680,65280],[41120,64250,43690,52428,65280],[41120,64250,52428,61680,65280],[41120,64250,52428,65280],[51400,43690,52428,61680,65280],[51400,43690,61680,65280],[51400,64250,43690,61680,65280],[64000,43690,52428,61680],[64000,43690,52428,61680,65280],[64000,64250,43690,52428,61680],[65278,43690,52428,61680,65280],[65530,43690,52428,61680,65280]])
  · decide +kernel
  · intro M hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact n3_2_39
    · exact n3_2_40
    · exact n3_2_41
    · exact n3_2_47
    · exact n3_2_48
    · exact n3_2_56
    · exact n3_2_59
    · exact n3_2_116
    · exact n3_2_117
    · exact n3_2_118
    · exact n3_2_156
    · exact n3_2_157
    · exact n3_2_212
    · exact n3_2_213
    · exact n3_2_214
    · exact n3_2_270
    · exact n3_2_271
    · exact n3_2_272
    · exact n3_2_351
    · exact n3_2_352
    · exact n3_2_353
    · exact n3_2_373
    · exact n3_2_402
private theorem n3_1_20 : find (dimension := 4) 59520 5 [64764,43690,52428,61680,65280] = false := by
  apply blocked_sound (known := [[252,43690,52428,61680],[252,43690,52428,61680,65280],[252,64764,43690,52428,61680],[514,43690,52428,61680,65280],[768,43690,52428,61680,65280],[3084,43690,52428,61680,65280],[3084,64764,43690,52428,65280],[12336,43690,52428,61680,65280],[12336,64764,43690,61680,65280],[21588,43690,52428,61680,65280],[21588,52428,61680,65280],[21588,64764,52428,61680,65280],[43176,43690,52428,61680,65280],[43176,52428,61680,65280],[43176,64764,52428,61680,65280],[49344,64764,43690,52428,65280],[49344,64764,43690,61680,65280],[49344,64764,43690,65280],[64512,43690,52428,61680],[64512,43690,52428,61680,65280],[64512,64764,43690,52428,61680],[65278,43690,52428,61680,65280],[65532,43690,52428,61680,65280]])
  · decide +kernel
  · intro M hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact n3_2_42
    · exact n3_2_43
    · exact n3_2_44
    · exact n3_2_45
    · exact n3_2_46
    · exact n3_2_67
    · exact n3_2_70
    · exact n3_2_111
    · exact n3_2_114
    · exact n3_2_159
    · exact n3_2_160
    · exact n3_2_161
    · exact n3_2_218
    · exact n3_2_219
    · exact n3_2_220
    · exact n3_2_264
    · exact n3_2_265
    · exact n3_2_266
    · exact n3_2_362
    · exact n3_2_363
    · exact n3_2_364
    · exact n3_2_373
    · exact n3_2_403
private theorem n3_1_21 : find (dimension := 4) 59520 5 [65450,43690,52428,61680,65280] = false := by
  apply blocked_sound (known := [[68,43690,52428,61680,65280],[80,43690,52428,61680,65280],[170,43690,52428,61680,65280],[170,65450,43690,52428,61680],[3850,43690,52428,61680,65280],[3850,43690,52428,65280],[3850,65450,43690,52428,65280],[13090,43690,52428,61680,65280],[13090,43690,61680,65280],[13090,65450,43690,61680,65280],[21760,43690,52428,61680,65280],[21760,65450,52428,61680,65280],[43520,65450,43690,52428,61680],[43520,65450,52428,61680],[43520,65450,52428,61680,65280],[52360,43690,52428,61680,65280],[52360,43690,61680,65280],[52360,65450,43690,61680,65280],[61600,43690,52428,61680,65280],[61600,43690,52428,65280],[61600,65450,43690,52428,65280],[65518,43690,52428,61680,65280],[65530,43690,52428,61680,65280]])
  · decide +kernel
  · intro M hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact n3_2_4
    · exact n3_2_5
    · exact n3_2_13
    · exact n3_2_16
    · exact n3_2_84
    · exact n3_2_85
    · exact n3_2_86
    · exact n3_2_128
    · exact n3_2_129
    · exact n3_2_130
    · exact n3_2_169
    · exact n3_2_170
    · exact n3_2_232
    · exact n3_2_233
    · exact n3_2_234
    · exact n3_2_289
    · exact n3_2_290
    · exact n3_2_291
    · exact n3_2_336
    · exact n3_2_337
    · exact n3_2_338
    · exact n3_2_395
    · exact n3_2_402
private theorem n3_1_22 : find (dimension := 4) 59520 5 [65484,43690,52428,61680,65280] = false := by
  apply blocked_sound (known := [[34,43690,52428,61680,65280],[48,43690,52428,61680,65280],[204,43690,52428,61680,65280],[204,65484,43690,52428,61680],[3852,43690,52428,61680,65280],[3852,43690,52428,65280],[3852,65484,43690,52428,65280],[13056,43690,52428,61680,65280],[13056,65484,43690,61680,65280],[21828,43690,52428,61680,65280],[21828,52428,61680,65280],[21828,65484,52428,61680,65280],[43656,43690,52428,61680,65280],[43656,52428,61680,65280],[43656,65484,52428,61680,65280],[52224,65484,43690,52428,61680],[52224,65484,43690,61680],[52224,65484,43690,61680,65280],[61632,43690,52428,61680,65280],[61632,43690,52428,65280],[61632,65484,43690,52428,65280],[65518,43690,52428,61680,65280],[65532,43690,52428,61680,65280]])
  · decide +kernel
  · intro M hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact n3_2_2
    · exact n3_2_3
    · exact n3_2_23
    · exact n3_2_26
    · exact n3_2_87
    · exact n3_2_88
    · exact n3_2_89
    · exact n3_2_124
    · exact n3_2_127
    · exact n3_2_171
    · exact n3_2_172
    · exact n3_2_173
    · exact n3_2_237
    · exact n3_2_238
    · exact n3_2_239
    · exact n3_2_284
    · exact n3_2_285
    · exact n3_2_286
    · exact n3_2_339
    · exact n3_2_340
    · exact n3_2_341
    · exact n3_2_395
    · exact n3_2_403
private theorem n3_1_23 : find (dimension := 4) 59520 5 [65520,43690,52428,61680,65280] = false := by
  apply blocked_sound (known := [[10,43690,52428,61680,65280],[12,43690,52428,61680,65280],[240,43690,52428,61680,65280],[240,65520,43690,52428,61680],[3840,43690,52428,61680,65280],[3840,65520,43690,52428,65280],[13104,43690,52428,61680,65280],[13104,43690,61680,65280],[13104,65520,43690,61680,65280],[21840,43690,52428,61680,65280],[21840,52428,61680,65280],[21840,65520,52428,61680,65280],[43680,43690,52428,61680,65280],[43680,52428,61680,65280],[43680,65520,52428,61680,65280],[52416,43690,52428,61680,65280],[52416,43690,61680,65280],[52416,65520,43690,61680,65280],[61440,65520,43690,52428],[61440,65520,43690,52428,61680],[61440,65520,43690,52428,65280],[65530,43690,52428,61680,65280],[65532,43690,52428,61680,65280]])
  · decide +kernel
  · intro M hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact n3_2_0
    · exact n3_2_1
    · exact n3_2_35
    · exact n3_2_38
    · exact n3_2_80
    · exact n3_2_83
    · exact n3_2_131
    · exact n3_2_132
    · exact n3_2_133
    · exact n3_2_174
    · exact n3_2_175
    · exact n3_2_176
    · exact n3_2_240
    · exact n3_2_241
    · exact n3_2_242
    · exact n3_2_292
    · exact n3_2_293
    · exact n3_2_294
    · exact n3_2_331
    · exact n3_2_332
    · exact n3_2_333
    · exact n3_2_402
    · exact n3_2_403
private theorem n3_0_0 : find (dimension := 4) 59520 6 [43690,52428,61680,65280] = false := by
  apply blocked_sound (known := [[170,43690,52428,61680,65280],[204,43690,52428,61680,65280],[240,43690,52428,61680,65280],[2570,43690,52428,61680,65280],[3084,43690,52428,61680,65280],[3840,43690,52428,61680,65280],[8738,43690,52428,61680,65280],[12336,43690,52428,61680,65280],[13056,43690,52428,61680,65280],[17476,43690,52428,61680,65280],[20560,43690,52428,61680,65280],[21760,43690,52428,61680,65280],[34952,43690,52428,61680,65280],[41120,43690,52428,61680,65280],[43520,43690,52428,61680,65280],[49344,43690,52428,61680,65280],[52224,43690,52428,61680,65280],[61166,43690,52428,61680,65280],[61440,43690,52428,61680,65280],[64250,43690,52428,61680,65280],[64764,43690,52428,61680,65280],[65450,43690,52428,61680,65280],[65484,43690,52428,61680,65280],[65520,43690,52428,61680,65280]])
  · decide +kernel
  · intro M hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact n3_1_0
    · exact n3_1_1
    · exact n3_1_2
    · exact n3_1_3
    · exact n3_1_4
    · exact n3_1_5
    · exact n3_1_6
    · exact n3_1_7
    · exact n3_1_8
    · exact n3_1_9
    · exact n3_1_10
    · exact n3_1_11
    · exact n3_1_12
    · exact n3_1_13
    · exact n3_1_14
    · exact n3_1_15
    · exact n3_1_16
    · exact n3_1_17
    · exact n3_1_18
    · exact n3_1_19
    · exact n3_1_20
    · exact n3_1_21
    · exact n3_1_22
    · exact n3_1_23

theorem lower3 {k T} (p : Steps (sources 4) k T) (out : threshold ∈ T) : 7 ≤ k :=
  lower_of_nodes threshold 59520 (by decide +kernel) 6 (by decide +kernel)
    ![6,5,3,3] ![7,7,7,11] (by decide +kernel) n3_0_0 p out
end PEqualNP.Outside.L_meta_1415.SmallThreshold

namespace PEqualNP.Outside.L_meta_1415.RestrictionLift
open PEqualNP.Outside.L_meta_1415.SignedWork PEqualNP.Outside.L_meta_1415.RestrictionWork

abbrev X := Fin 5 → Bool
abbrev Y := Fin 4 → Bool

def five (count : Nat) (x : X) : Bool := decide (count ≤ (List.ofFn x).count true)
def four (count : Nat) (x : Y) : Bool := decide (count ≤ (List.ofFn x).count true)
def coord {n : Nat} (i : Fin (n+1)) (x : Fin n → Bool) : Bool :=
  if h : i.val < n then x ⟨i.val,h⟩ else false

def pin (i : Fin 5) (value : Bool) (x : Y) (j : Fin 5) : Bool :=
  if i=j then value else if h : j.val < 4 then x ⟨j.val,h⟩ else x ⟨i.val % 4,by omega⟩

private theorem listed {n : Nat} {s : Fn (Fin n → Bool)} :
    s ∈ sources n ↔ ∃ i : Fin (n+1), coord i = s := by
  constructor
  · rintro (rfl|⟨i,rfl⟩)
    · exact ⟨Fin.last n, by funext x; simp [coord,zeroF]⟩
    · exact ⟨i.castSucc,by funext x; simp [coord]⟩
  · rintro ⟨i,rfl⟩
    by_cases h : i.val < n
    · exact .inr ⟨⟨i.val,h⟩,by funext x; simp [coord,h]⟩
    · exact .inl (by funext x; simp [coord,h,zeroF])

private theorem source_image (i : Fin 5) (v : Bool) :
    project (pin i v) (fun _ => false) '' sources 5 = sources 4 := by
  ext f
  constructor
  · rintro ⟨s,h,rfl⟩
    obtain ⟨a,rfl⟩ := listed.mp h
    exact listed.mpr ((by decide +kernel :
      ∀ (i : Fin 5) (v : Bool) (a : Fin 6), ∃ b : Fin 5,
        coord b = project (pin i v) (fun _ => false) (coord a)) i v a)
  · intro hf
    obtain ⟨b,rfl⟩ := listed.mp hf
    obtain ⟨a,e⟩ := (by decide +kernel : ∀ (i : Fin 5) (v : Bool) (b : Fin 5), ∃ a : Fin 6,
      project (pin i v) (fun _ => false) (coord a) = coord b) i v b
    exact ⟨_,listed.mpr ⟨a,rfl⟩,e⟩

private theorem peel {S U : Set (Fn X)} {k} (s : Steps S k U) :
    (k=0 ∧ U=S) ∨ ∃ (a b : Fn X) (v : Fin 4) (m : Nat),
      a ∈ S ∧ b ∈ S ∧ m+1=k ∧ Steps (insert (operation v a b) S) m U := by
  induction s with
  | start => exact .inl ⟨rfl,rfl⟩
  | append p v ha hb ih =>
    rcases ih with ⟨rfl,rfl⟩|⟨a,b,t,m,ia,ib,len,h⟩
    · exact .inr ⟨_,_,v,0,ha,hb,rfl,.start⟩
    · exact .inr ⟨a,b,t,m+1,ia,ib,by omega,h.append v ha hb⟩

def truthRow (r : Fin 32) (i : Fin 5) : Bool := r.val.testBit i.val
def firstSig (v : Fin 4) (a b : Fin 6) : Fn X := operation v (coord a) (coord b)

-- Finite witnesses choose the fixed coordinate, a name for the projected first
-- signal, and two rows distinguished by the target but not by that signal.
def cert (cut : Bool) (v : Fin 4) (a b : Fin 6) : Fin 5 × Fin 5 × Fin 32 :=
  (if cut then ![![![(1,0,13),(0,4,14),(0,4,14),(0,4,14),(0,4,22),(1,0,13)],![(0,4,14),(0,1,14),(1,4,13),(1,4,13),(1,4,21),(0,1,14)],![(0,4,14),(1,4,13),(0,2,14),(2,4,11),(2,4,19),(0,2,14)],![(0,4,14),(1,4,13),(2,4,11),(0,3,14),(3,4,19),(0,3,14)],![(0,4,22),(1,4,21),(2,4,19),(3,4,19),(0,0,14),(0,0,14)],![(1,0,13),(0,1,14),(0,2,14),(0,3,14),(0,0,14),(0,4,14)]],![![(1,0,13),(0,1,28),(0,2,26),(0,3,22),(0,0,14),(0,4,14)],![(0,1,28),(0,1,14),(1,2,25),(1,3,21),(1,1,13),(0,4,14)],![(0,2,26),(1,2,25),(0,2,14),(2,3,19),(2,2,11),(0,4,14)],![(0,3,22),(1,3,21),(2,3,19),(0,3,14),(3,3,7),(0,4,14)],![(0,0,14),(1,1,13),(2,2,11),(3,3,7),(0,0,14),(0,4,14)],![(0,4,14),(0,4,14),(0,4,14),(0,4,14),(0,4,14),(0,4,14)]],![![(0,4,14),(0,1,14),(0,2,14),(0,3,14),(0,0,22),(1,0,13)],![(0,4,28),(0,4,14),(1,2,13),(1,3,13),(1,1,21),(0,1,14)],![(0,4,26),(1,4,25),(0,4,14),(2,3,11),(2,2,19),(0,2,14)],![(0,4,22),(1,4,21),(2,4,19),(0,4,14),(3,3,19),(0,3,14)],![(0,4,14),(1,4,13),(2,4,11),(3,4,7),(0,4,14),(0,0,14)],![(0,4,14),(0,4,14),(0,4,14),(0,4,14),(0,4,14),(0,4,14)]],![![(0,4,14),(0,4,28),(0,4,26),(0,4,22),(0,4,14),(0,4,14)],![(0,1,14),(0,4,14),(1,4,25),(1,4,21),(1,4,13),(0,4,14)],![(0,2,14),(1,2,13),(0,4,14),(2,4,19),(2,4,11),(0,4,14)],![(0,3,14),(1,3,13),(2,3,11),(0,4,14),(3,4,7),(0,4,14)],![(0,0,22),(1,1,21),(2,2,19),(3,3,19),(0,4,14),(0,4,14)],![(1,0,13),(0,1,14),(0,2,14),(0,3,14),(0,0,14),(0,4,14)]]] else ![![![(1,0,1),(0,1,2),(0,2,4),(0,3,8),(0,0,16),(1,0,1)],![(0,1,2),(0,1,2),(1,2,4),(1,3,8),(1,1,16),(0,1,2)],![(0,2,4),(1,2,4),(0,2,2),(2,3,8),(2,2,16),(0,2,2)],![(0,3,8),(1,3,8),(2,3,8),(0,3,2),(3,3,16),(0,3,2)],![(0,0,16),(1,1,16),(2,2,16),(3,3,16),(0,0,2),(0,0,2)],![(1,0,1),(0,1,2),(0,2,2),(0,3,2),(0,0,2),(0,4,2)]],![![(1,0,1),(0,4,4),(0,4,2),(0,4,2),(0,4,2),(0,4,2)],![(0,4,4),(0,1,2),(1,4,1),(1,4,1),(1,4,1),(0,4,2)],![(0,4,2),(1,4,1),(0,2,2),(2,4,1),(2,4,1),(0,4,2)],![(0,4,2),(1,4,1),(2,4,1),(0,3,2),(3,4,1),(0,4,2)],![(0,4,2),(1,4,1),(2,4,1),(3,4,1),(0,0,2),(0,4,2)],![(0,4,2),(0,4,2),(0,4,2),(0,4,2),(0,4,2),(0,4,2)]],![![(0,4,2),(0,4,2),(0,4,4),(0,4,8),(0,4,16),(1,0,1)],![(0,1,4),(0,4,2),(1,4,4),(1,4,8),(1,4,16),(0,1,2)],![(0,2,2),(1,2,1),(0,4,2),(2,4,8),(2,4,16),(0,2,2)],![(0,3,2),(1,3,1),(2,3,1),(0,4,2),(3,4,16),(0,3,2)],![(0,0,2),(1,1,1),(2,2,1),(3,3,1),(0,4,2),(0,0,2)],![(0,4,2),(0,4,2),(0,4,2),(0,4,2),(0,4,2),(0,4,2)]],![![(0,4,2),(0,1,4),(0,2,2),(0,3,2),(0,0,2),(0,4,2)],![(0,4,2),(0,4,2),(1,2,1),(1,3,1),(1,1,1),(0,4,2)],![(0,4,4),(1,4,4),(0,4,2),(2,3,1),(2,2,1),(0,4,2)],![(0,4,8),(1,4,8),(2,4,8),(0,4,2),(3,3,1),(0,4,2)],![(0,4,16),(1,4,16),(2,4,16),(3,4,16),(0,4,2),(0,4,2)],![(1,0,1),(0,1,2),(0,2,2),(0,3,2),(0,0,2),(0,4,2)]]] : Fin 4 → Fin 6 → Fin 6 → Fin 5 × Fin 5 × Fin 32) v a b

private theorem verified (cut : Bool) (v : Fin 4) (a b : Fin 6) :
    let (i,z,r) := cert cut v a b
    let p := truthRow r
    let q := Function.update p i true
    let f := five (if cut then 4 else 2)
    let g := firstSig v a b
    project (pin i cut) (fun _ => false) g = coord z ∧
      g p = g q ∧ f p ≠ f q := by
  exact (by decide +kernel : ∀ (c : Bool) (u : Fin 4) (x y : Fin 6),
    let (i,z,r) := cert c u x y
    let p := truthRow r
    let q := Function.update p i true
    let f := five (if c then 4 else 2)
    let g := firstSig u x y
    project (pin i c) (fun _ => false) g = coord z ∧ g p = g q ∧ f p ≠ f q) cut v a b

theorem lift_bound (cut : Bool)
    (cofactor : ∀ j V, Steps (sources 4) j V → four (if cut then 3 else 2) ∈ V → 7 ≤ j)
    {k U} (path : Steps (sources 5) k U) (hit : five (if cut then 4 else 2) ∈ U) : 9 ≤ k := by
  let f := five (if cut then 4 else 2)
  have nonsrc : f ∉ sources 5 := by
    intro h
    obtain ⟨a,e⟩ := listed.mp h
    exact (by decide +kernel : ∀ (c : Bool) (a : Fin 6), coord a ≠ five (if c then 4 else 2)) cut a e
  rcases peel path with ⟨_,rfl⟩|⟨a,b,v,m,ha,hb,num,suffix⟩
  · exact (nonsrc hit).elim
  obtain ⟨i,rfl⟩ := listed.mp ha
  obtain ⟨j,rfl⟩ := listed.mp hb
  let g := firstSig v i j
  obtain ⟨t,z,r,e⟩ : ∃ t z r, cert cut v i j = (t,z,r) := ⟨_,_,_,rfl⟩
  have ok := verified cut v i j
  rw [e] at ok
  obtain ⟨pr,mask,diff⟩ := ok
  let p := truthRow r
  let q := Function.update p t true
  have other : f ∉ insert g (sources 5) := by
    rintro (eq|mem)
    · have hn := (by decide +kernel : ∀ (c : Bool) v i j,
        five (if c then 4 else 2) ≠ firstSig v i j) cut v i j
      exact hn eq
    · exact nonsrc mem
  have base : ∀ s ∈ insert g (sources 5), s p ≠ s q → project (pin t cut) (fun _ => false) s = zeroF := by
    rintro s (rfl|hs) neq
    · exact (neq mask).elim
    · rcases hs with rfl|⟨u,rfl⟩
      · exact (neq rfl).elim
      · by_cases eq : u = t
        · subst u; funext x; simp [project,canonical,pin,zeroF]
        · exact (neq (Function.update_of_ne eq ..).symm).elim
  obtain ⟨j',run,small⟩ := essential_restriction (pin t cut) (fun _ => false) suffix hit p q diff other base
  have proj : project (pin t cut) (fun _ => false) f = four (if cut then 3 else 2) :=
    (by decide +kernel : ∀ (c : Bool) (t : Fin 5), project (pin t c) (fun _ => false)
      (five (if c then 4 else 2)) = four (if c then 3 else 2)) cut t
  have member := Set.mem_image_of_mem (project (pin t cut) (fun _ => false)) hit
  change project (pin t cut) (fun _ => false) f ∈ _ at member
  rw [proj] at member
  rw [Set.image_insert_eq,source_image] at run
  change Steps (insert (project (pin t cut) (fun _ => false) g) (sources 4)) _ _ at run
  rw [pr,Set.insert_eq_of_mem (listed.mpr ⟨z,rfl⟩)] at run
  have := cofactor _ _ run member
  omega

end PEqualNP.Outside.L_meta_1415.RestrictionLift

namespace PEqualNP.Outside.L_meta_1415.ThresholdCost
open PEqualNP.Outside.L_meta_1415.SignedWork PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1415.RestrictionLift

theorem transfer (cut : Bool) (T : Nat) (table : PEqualNP.Outside.L_meta_1415_aux.evalT T = five (if cut then 4 else 2))
    (cofactor : ∀ k U, Steps (sources 4) k U → four (if cut then 3 else 2) ∈ U → 7 ≤ k)
    (gs : List Gate) (o : Nat) (legal : FanInTwo (⟨gs,o⟩ : Circuit))
    (correct : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = PEqualNP.Outside.L_meta_1415_aux.evalT T x) :
    (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∨ 10 ≤ gs.length := by
  by_cases pure : ∀ g ∈ gs, g.op ≠ .not
  · left
    intro g mem
    have ⟨alt,arity⟩ := legal g mem
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at alt
    exact ⟨alt.elim Or.inl (fun h => Or.inr (h.resolve_right (pure g mem))),arity⟩
  · right
    push Not at pure
    obtain ⟨w,mem,isnot⟩ := pure
    have z : five (if cut then 4 else 2) (fun _ => false) = false := by cases cut <;> decide +kernel
    obtain ⟨m,U,path,out,bound⟩ := signed_budget (⟨gs,o⟩ : Circuit) legal _ z
      (fun x => (correct x).trans (congrFun table x))
    have lower := lift_bound cut cofactor path out
    have keep : PEqualNP.Outside.L_meta_1415.SignedWork.isNot w = true := by simp [PEqualNP.Outside.L_meta_1415.SignedWork.isNot,isnot]
    have h : 0 < (gs.filter PEqualNP.Outside.L_meta_1415.SignedWork.isNot).length :=
      List.length_pos_of_mem (List.mem_filter.mpr ⟨mem,keep⟩)
    change m + (gs.filter PEqualNP.Outside.L_meta_1415.SignedWork.isNot).length ≤ gs.length at bound
    omega
end PEqualNP.Outside.L_meta_1415.ThresholdCost

namespace PEqualNP.Outside.L_meta_1415_aux
open PEqualNP.CircuitLowerBounds

lemma table6 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ a b : Fin gs.length, (gs.get a).op = .not → (gs.get b).op = .not → a = b)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3900735488 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 3900735488 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have result := PEqualNP.Outside.L_meta_1415.ThresholdCost.transfer true _ (by decide +kernel)
    (fun k U path hit => PEqualNP.Outside.L_meta_1415.SmallThreshold.lower3 path hit) gs o legal he
  rcases result with pure|bound
  · exact ⟨gs,o,pure,Nat.le_refl _,he⟩
  · exact ⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 1]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [4, 6]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [11, 13]⟩], 14, by simp, by exact bound, by decide +kernel⟩

def raw7 : List Sig := [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0xa924925492492a49249524924a924925492492a49249524924a924925492492a),
  (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0x3249249924924c924926492493249249924924c924926492493249249924924c),
  (0x3fffffe000000ffffffffffffc000001ffffff0000007fffffc000001ffffff, 0xc38e38e1c71c70e38e3871c71c38e38e1c71c70e38e3871c71c38e38e1c71c70),
  (0x3ffffffffffff0000007fffffffffffe0000000000007fffffffffffe000000, 0x3f03f01f81f80fc0fc07e07e03f03f01f81f80fc0fc07e07e03f03f01f81f80),
  (0xfc0000000000000000007ffffffffffffffffffffffff8000000000000000000, 0x3ffc001ffe000fff0007ff8003ffc001ffe000fff0007ff8003ffc001ffe000)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut7Zero : search 3 0 raw7 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut7One : search 3 1 raw7 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma table7 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ a b : Fin gs.length, (gs.get a).op = .not → (gs.get b).op = .not → a = b)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 2290649216 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 2290649216 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have bound := cost 2290649216 raw7 3 rfl (by decide +kernel) (by decide +kernel)
    rfl (by decide +kernel) (by
      intro t
      fin_cases t
      · exact ruledOut7Zero
      · exact ruledOut7One) ⟨gs,o⟩ legal hn he
  exact ⟨[⟨.or, [3, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [0, 7]⟩], 8, by simp, by exact Nat.succ_le_of_lt bound, by decide +kernel⟩

def raw8 : List Sig := [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0xa84a925425492a12a49509524a84a925425492a12a49509524a84a925425492a),
  (0xffffffffffffffffffffffffffc000001fffffffffffffffffffffffffffffff, 0x3293249949924ca4c926526493293249949924ca4c926526493293249949924c),
  (0xfffffffe000000ffffffffffffffffffe000000ffffffffffffc000001ffffff, 0xc31c38e18e1c70c70e3863871c31c38e18e1c70c70e3863871c31c38e18e1c70),
  (0x3ffffffffffff0000007ffffffffffffffffff0000007fffffffffffe000000, 0x3e03f01f01f80f80fc07c07e03e03f01f01f80f80fc07c07e03e03f01f01f80),
  (0xfc0000000000000000007ffffffffffffffffffffffff8000000000000000000, 0x3ffc001ffe000fff0007ff8003ffc001ffe000fff0007ff8003ffc001ffe000)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut8Zero : search 5 0 raw8 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut8One : search 5 1 raw8 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma table8 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ a b : Fin gs.length, (gs.get a).op = .not → (gs.get b).op = .not → a = b)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 2826995840 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 2826995840 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have bound := cost 2826995840 raw8 5 rfl (by decide +kernel) (by decide +kernel)
    rfl (by decide +kernel) (by
      intro t
      fin_cases t
      · exact ruledOut8Zero
      · exact ruledOut8One) ⟨gs,o⟩ legal hn he
  exact ⟨[⟨.and, [1, 2]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [3, 7]⟩, ⟨.or, [5, 8]⟩, ⟨.and, [0, 9]⟩], 10, by simp, by exact Nat.succ_le_of_lt bound, by decide +kernel⟩

def raw9 : List Sig := [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0xa8491554248aaa1245550922aa8491554248aaa1245550922aa8491554248aaa),
  (0xffffffffffffff0000007fffffc000001ffffffffffffffffffffffffe000000, 0x32925999492ccca49666524b332925999492ccca49666524b332925999492ccc),
  (0xfc000001ffffffffffffffffffffffffe000000ffffff8000003ffffffffffff, 0xc31c61e18e30f0c71878638c3c31c61e18e30f0c71878638c3c31c61e18e30f0),
  (0x1fffffffffffffffffffffffffffffff0000000000003ffffffffffff, 0x3e07e01f03f00f81f807c0fc03e07e01f03f00f81f807c0fc03e07e01f03f00),
  (0xfffffffe0000000000007ffffffffffffffffffffffffffffffc000000000000, 0x3ff8001ffc000ffe0007ff0003ff8001ffc000ffe0007ff0003ff8001ffc000)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut9Zero : search 3 0 raw9 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut9One : search 3 1 raw9 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma table9 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ a b : Fin gs.length, (gs.get a).op = .not → (gs.get b).op = .not → a = b)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 2827526144 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 2827526144 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have bound := cost 2827526144 raw9 3 rfl (by decide +kernel) (by decide +kernel)
    rfl (by decide +kernel) (by
      intro t
      fin_cases t
      · exact ruledOut9Zero
      · exact ruledOut9One) ⟨gs,o⟩ legal hn he
  exact ⟨[⟨.and, [1, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [0, 7]⟩], 8, by simp, by exact Nat.succ_le_of_lt bound, by decide +kernel⟩

end PEqualNP.Outside.L_meta_1415_aux

open PEqualNP.Outside.L_meta_1415_aux in
theorem PEqualNP.Outside.L_meta_1415 :
  ∀ T ∈ ({0x80000000, 0x80808000, 0x88808000, 0x88808080, 0xa8808000, 0xa8808080, 0xe8808000, 0x88888880, 0xa8808880, 0xa888a000} : Finset ℕ), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro T hT gs o legal single correct
  simp only [Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact table0 gs o legal single correct
  · exact table1 gs o legal single correct
  · exact table2 gs o legal single correct
  · exact table3 gs o legal single correct
  · exact table4 gs o legal single correct
  · exact table5 gs o legal single correct
  · exact table6 gs o legal single correct
  · exact table7 gs o legal single correct
  · exact table8 gs o legal single correct
  · exact table9 gs o legal single correct
